#!/usr/bin/env python3
"""dbuild: distributed DAG runner for per-module Lean jobs (build / kernel replay).

One coordinator holds the import DAG and hands modules to node workers over TCP
(newline-delimited JSON).  A worker runs up to SLOTS jobs at once, each inside a
bwrap sandbox (no network, read-only filesystem, one private writable dir), and
moves the produced files into place itself.  Stdlib only.

  coordinator:  dbuild.py coord --conf conf.json [--mode build|replay] [--roots A,B]
  worker:       dbuild.py work  --state STATE_DIR [--slots N] [--sandbox auto|bwrap|none]

conf.json keys: graph, src, out, state, lean (path to lean binary dir), lean_path (list of
olean roots of dependencies), lib_opts ({prefix: [extra args]}), args (common lean args),
threads, timeout.
State (STATE_DIR): coord.addr, results.jsonl (one line per finished attempt), summary.json.
Resume = start the coordinator again: modules with a successful result and an existing
output file are skipped.
"""
import argparse, collections, heapq, json, os, re, selectors, shutil, signal, socket
import subprocess, sys, threading, time

# ----------------------------------------------------------------------------- common


def send(sock, lock, obj):
    data = (json.dumps(obj, separators=(',', ':')) + '\n').encode()
    with lock:
        sock.sendall(data)


def mod_rel(mod):
    return mod.replace('.', '/')


# ----------------------------------------------------------------------------- coordinator

class Coord:
    def __init__(self, conf, mode, roots, limit):
        for k in ('graph', 'src', 'out', 'state', 'lean'):
            conf[k] = os.path.realpath(conf[k])
        conf['lean_path'] = [os.path.realpath(p) for p in conf.get('lean_path', [])]
        os.makedirs(os.path.join(conf['out'], 'lib'), exist_ok=True)
        if conf.get('preload'):
            conf['preload'] = os.path.realpath(conf['preload'])
        self.conf, self.mode = conf, mode
        self.closure = {}
        if conf.get('closure') and os.path.exists(conf['closure']):
            for line in open(conf['closure']):
                c, m = line.rstrip('\n').split('\t')
                self.closure[m] = int(c)
        self.state = conf['state']
        os.makedirs(self.state, exist_ok=True)
        graph = json.load(open(conf['graph']))
        if roots:
            keep, st = set(), [r for r in roots if r in graph]
            while st:
                m = st.pop()
                if m not in keep:
                    keep.add(m)
                    st.extend(graph[m]['imports'])
            graph = {m: graph[m] for m in keep}
        if mode == 'replay' and conf.get('replay_deps', True):
            # dependency oleans (Mathlib & co, from the download cache) get kernel-replayed too
            n0 = len(graph)
            for lp in conf['lean_path']:
                for d, _, fs in os.walk(lp):
                    for f in fs:
                        if f.endswith('.olean'):
                            p = os.path.join(d, f)
                            m = os.path.relpath(p, lp)[:-6].replace('/', '.')
                            graph.setdefault(m, {'size': os.path.getsize(p) // 20, 'imports': [], 'ext': []})
            print(f'[coord] replay: {n0} project modules + {len(graph) - n0} dependency modules', flush=True)
        self.graph = graph
        self.results_path = os.path.join(self.state, f'results-{mode}.jsonl')
        self.cost = {m: float(g['size']) + 20000.0 for m, g in graph.items()}  # bytes proxy (+import overhead)
        self.done, self.failed, self.attempts = set(), {}, collections.Counter()
        self.weight = {}
        for m, cnt in self.closure.items():
            w = 1 if cnt < 12000 else 2 if cnt < 20000 else 6 if cnt < 30000 else 24 if cnt < 45000 else 64 if cnt < 90000 else 112
            if w > 1 and m in graph:
                self.weight[m] = w
        self.cpu_s = 0.0
        self._load_previous()
        self.rev = collections.defaultdict(list)
        self.npend = {}
        for m, g in graph.items():
            deps = g['imports'] if mode == 'build' else []
            self.npend[m] = sum(1 for d in deps if d not in self.done)
            for d in deps:
                self.rev[d].append(m)
        self._priorities()
        self.ready = [(-self.prio[m], m) for m in graph if m not in self.done and self.npend[m] == 0]
        if limit:
            self.ready = self.ready[:limit]
            self.limit_set = {m for _, m in self.ready}
        else:
            self.limit_set = None
        heapq.heapify(self.ready)
        self.heavy = []                       # (weight, module) needing >1 slot
        self.workers = {}                     # sock -> dict
        self.running = {}                     # job id -> (module, sock, start)
        self.next_id = 0
        self.t0 = time.time()
        self.res_f = open(self.results_path, 'a')
        self.total = len(graph) if not limit else len(self.limit_set) + len(self.done)
        self.done_bytes0 = sum(self.cost[m] for m in self.done)
        self.sess_cost = 0.0

    def _out_file(self, m):
        if self.mode == 'build':
            return os.path.join(self.conf['out'], 'lib', mod_rel(m) + '.olean')
        return None

    def _load_previous(self):
        if not os.path.exists(self.results_path):
            return
        ok, t = set(), {}
        for line in open(self.results_path):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r['mod'] not in self.graph:
                continue
            if r['rc'] == 0:
                ok.add(r['mod'])
                t[r['mod']] = r.get('cpu', 0)
            elif r.get('oom'):
                self.weight[r['mod']] = min(64, max(self.weight.get(r['mod'], 1) * 4, 4))
        for m in ok:
            f = self._out_file(m)
            if f is None or os.path.exists(f):
                self.done.add(m)
        print(f'[coord] resume: {len(self.done)} modules already done', flush=True)

    def _priorities(self):
        # bottom level: own cost + heaviest chain of dependents => critical-path-first scheduling
        order, indeg = [], {m: len(self.graph[m]['imports']) if self.mode == 'build' else 0 for m in self.graph}
        q = collections.deque(m for m, d in indeg.items() if d == 0)
        while q:
            m = q.popleft()
            order.append(m)
            for d in self.rev[m]:
                indeg[d] -= 1
                if indeg[d] == 0:
                    q.append(d)
        if len(order) != len(self.graph):
            sys.exit(f'[coord] import cycle: {len(self.graph) - len(order)} modules unsortable')
        self.prio = {}
        for m in reversed(order):
            self.prio[m] = self.cost[m] + max((self.prio[d] for d in self.rev[m]), default=0.0)
        if self.mode != 'build':            # no deps: biggest first
            self.prio = dict(self.cost)

    # -- job construction
    def job_for(self, m):
        c = self.conf
        self.next_id += 1
        src = os.path.join(c['src'], mod_rel(m) + '.lean')
        files = {}
        if self.mode == 'build':
            opts = dict(c.get('options', {}))
            for pref, o in c.get('lib_opts', {}).items():
                if m.startswith(pref):
                    opts.update(o)
            # same invocation lake uses (minus -i/-c): options and module name travel in the setup file
            files['setup.json'] = json.dumps({'plugins': [], 'package': c.get('package', 'tree'), 'options': opts,
                                              'name': m, 'isModule': False, 'importArts': {}, 'dynlibs': []})
            argv = [os.path.join(c['lean'], 'lean')] + c.get('args', []) + \
                   [src, '-o', '@TMP@/m.olean', '--setup', '@TMP@/setup.json', '--json']
            if c.get('threads'):
                argv += ['-j', str(c['threads'])]
            moves = [['m.olean', self._out_file(m)]]
        else:
            argv = [os.path.join(c['lean'], 'leanchecker'), m]
            moves = []
        lp = ':'.join(c.get('lean_path', []) + [os.path.join(c['out'], 'lib')])
        env = {'LEAN_PATH': lp}
        ro_extra = []
        if c.get('preload'):                 # rhshim.so: see rhshim.c (low vm.max_map_count workaround)
            env['LD_PRELOAD'] = c['preload']
            ro_extra.append(os.path.dirname(c['preload']))
        return {'t': 'job', 'id': self.next_id, 'mod': m, 'argv': argv, 'moves': moves, 'files': files,
                'env': env,
                'cwd': c['src'], 'timeout': c.get('timeout', 14400), 'weight': self.weight.get(m, 1),
                'ro': [c['src'], os.path.dirname(c['lean'])] + ro_extra + c.get('lean_path', []) + [os.path.join(c['out'], 'lib')]}

    # -- scheduling
    def dispatch(self):
        ws = [w for w in self.workers.values() if w['free'] > 0 and w.get('ready')]
        if not ws:
            return
        # heavy jobs first: reserve the emptiest worker until the job fits
        still = []
        for wt, m in self.heavy:
            w = max(ws, key=lambda w: w['free']) if ws else None
            need = min(wt, w['slots']) if w else wt
            if w and w['free'] >= need:
                self._start(w, m, need)
            else:
                if w:
                    w['hold'] = True
                still.append((wt, m))
        self.heavy = still
        ws.sort(key=lambda w: -w['free'])
        for w in ws:
            if w.pop('hold', False):
                continue
            while w['free'] > 0 and self.ready:
                _, m = heapq.heappop(self.ready)
                wt = self.weight.get(m, 1)
                if wt > 1:
                    self.heavy.append((wt, m))
                    continue
                self._start(w, m, 1)

    def _start(self, w, m, slots):
        job = self.job_for(m)
        job['weight'] = slots
        w['free'] -= slots
        w['jobs'][job['id']] = (m, slots)
        self.running[job['id']] = (m, w['sock'], time.time())
        try:
            send(w['sock'], w['lock'], job)
        except OSError:
            pass                              # the drop is handled by the reader

    def on_done(self, w, r):
        m, slots = w['jobs'].pop(r['id'])
        self.running.pop(r['id'], None)
        w['free'] += slots
        self.attempts[m] += 1
        self.cpu_s += r.get('cpu', 0)
        rec = {k: r[k] for k in ('mod', 'rc', 'wall', 'cpu', 'rss', 'oom', 'timeout') if k in r}
        rec.update(host=w['host'], n=self.attempts[m], slots=slots, ts=round(time.time(), 1))
        if r['rc'] != 0 or r.get('out'):
            rec['out'] = r.get('out', '')[-20000:]
        self.res_f.write(json.dumps(rec, ensure_ascii=False) + '\n')
        self.res_f.flush()
        if r['rc'] == 0:
            self.done.add(m)
            self.sess_cost += self.cost[m]
            for d in self.rev[m]:
                self.npend[d] -= 1
                if self.npend[d] == 0 and d not in self.done and (self.limit_set is None or d in self.limit_set):
                    heapq.heappush(self.ready, (-self.prio[d], d))
        elif r.get('oom') and slots < w['slots']:
            self.weight[m] = min(w['slots'], max(4, slots * 4))
            self.heavy.append((self.weight[m], m))
        elif self.attempts[m] < 2 and not r.get('timeout'):
            print(f"[coord] retrying {m} (rc={r['rc']} on {w['host']})", flush=True)
            heapq.heappush(self.ready, (-self.prio[m], m))
        else:
            self.failed[m] = rec
            print(f"[coord] FAILED {m} rc={r['rc']} on {w['host']}: {r.get('out', '')[-600:]!r}", flush=True)

    def drop(self, w):
        for jid, (m, slots) in list(w['jobs'].items()):
            self.running.pop(jid, None)
            heapq.heappush(self.ready, (-self.prio[m], m))
        print(f"[coord] worker {w.get('host')} gone, requeued {len(w['jobs'])} jobs", flush=True)
        self.workers.pop(w['sock'], None)

    def status(self):
        el = time.time() - self.t0
        rate = self.sess_cost / el if el > 0 else 0
        left = sum(self.cost[m] for m in self.graph if m not in self.done)
        eta = left / rate / 3600 if rate > 0 else float('nan')
        slots = sum(w['slots'] for w in self.workers.values())
        print(f"[coord] {time.strftime('%H:%M:%S')} done {len(self.done)}/{self.total} running {len(self.running)} "
              f"ready {len(self.ready)} heavy {len(self.heavy)} failed {len(self.failed)} workers {len(self.workers)} "
              f"slots {slots} cpu-h {self.cpu_s / 3600:.1f} elapsed {el / 3600:.2f}h eta~{eta:.2f}h", flush=True)

    def finished(self):
        return not self.running and not self.ready and not self.heavy

    def run(self, port, idle_exit):
        srv = socket.socket()
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind(('0.0.0.0', port))
        srv.listen(1024)
        addr = f'{socket.gethostname()}:{srv.getsockname()[1]}'
        with open(os.path.join(self.state, 'coord.addr.tmp'), 'w') as f:
            f.write(addr)
        os.replace(os.path.join(self.state, 'coord.addr.tmp'), os.path.join(self.state, 'coord.addr'))
        print(f'[coord] listening on {addr}; mode={self.mode} todo={self.total - len(self.done)} of {self.total}', flush=True)
        sel = selectors.DefaultSelector()
        sel.register(srv, selectors.EVENT_READ)
        last, had_worker = time.time(), False
        while True:
            if self.finished() and (had_worker or self.total == len(self.done)):
                break
            for key, _ in sel.select(timeout=5):
                s = key.fileobj
                if s is srv:
                    c, _ = srv.accept()
                    c.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                    self.workers[c] = {'sock': c, 'lock': threading.Lock(), 'buf': b'', 'jobs': {}, 'free': 0, 'slots': 0}
                    sel.register(c, selectors.EVENT_READ)
                    continue
                w = self.workers.get(s)
                try:
                    data = s.recv(1 << 20)
                except OSError:
                    data = b''
                if not data:
                    sel.unregister(s)
                    s.close()
                    if w:
                        self.drop(w)
                    continue
                w['buf'] += data
                while b'\n' in w['buf']:
                    line, w['buf'] = w['buf'].split(b'\n', 1)
                    msg = json.loads(line)
                    if msg['t'] == 'hello':
                        w.update(host=msg['host'], slots=msg['slots'], free=msg['slots'])
                        had_worker = True
                        send(s, w['lock'], {'t': 'conf', 'lean_path': self.conf['lean_path']})
                        print(f"[coord] worker {msg['host']} slots={msg['slots']} mem={msg.get('mem_gb')}G sandbox={msg.get('sandbox')}", flush=True)
                    elif msg['t'] == 'ready':
                        w['ready'] = True
                    elif msg['t'] == 'done':
                        self.on_done(w, msg)
            self.dispatch()
            if time.time() - last > 30:
                self.status()
                last = time.time()
            if idle_exit and had_worker and not self.workers:
                print('[coord] all workers gone', flush=True)
                break
        self.status()
        for w in list(self.workers.values()):
            try:
                send(w['sock'], w['lock'], {'t': 'quit'})
            except OSError:
                pass
        blocked = [m for m in self.graph if m not in self.done and m not in self.failed]
        summ = {'mode': self.mode, 'total': self.total, 'done': len(self.done), 'failed': sorted(self.failed),
                'blocked_or_unrun': len(blocked), 'cpu_hours': self.cpu_s / 3600, 'wall_hours': (time.time() - self.t0) / 3600}
        json.dump(summ, open(os.path.join(self.state, f'summary-{self.mode}.json'), 'w'), indent=1)
        print('[coord] summary', json.dumps({k: (v if k != 'failed' else len(v)) for k, v in summ.items()}), flush=True)
        try:
            os.remove(os.path.join(self.state, 'coord.addr'))
        except OSError:
            pass
        return 0 if len(self.done) == self.total else 1


# ----------------------------------------------------------------------------- worker

class Worker:
    def __init__(self, a):
        self.a = a
        self.host = socket.gethostname()
        self.slots = a.slots or len(os.sched_getaffinity(0))
        self.tmp_root = os.path.join(a.tmp or os.environ.get('TMPDIR') or '/tmp', f'dbuild-{os.getuid()}-{os.getpid()}')
        os.makedirs(self.tmp_root, exist_ok=True)
        self.sandbox = self._pick_sandbox(a.sandbox)
        self.stage = {}                       # shared path -> node-local copy
        self.procs = {}                       # job id -> Popen
        self.oomed = set()
        self.lock = threading.Lock()
        self.plock = threading.Lock()

    def _pick_sandbox(self, want):
        """bwrap where user namespaces exist (chili); singularity where they do not (LUMI compute nodes)."""
        if want == 'none':
            print(f'[work {self.host}] WARNING: running UNSANDBOXED by request', flush=True)
            return 'none'
        null = subprocess.DEVNULL
        bw = shutil.which('bwrap')
        if want in ('auto', 'bwrap') and bw and subprocess.run(
                [bw, '--unshare-net', '--ro-bind', '/', '/', '--dev', '/dev', 'true'], stdout=null, stderr=null).returncode == 0:
            return 'bwrap'
        sg, img = shutil.which('singularity') or shutil.which('apptainer'), self.a.image
        if want in ('auto', 'singularity') and sg and img and subprocess.run(
                [sg, 'exec', '--containall', '--no-home', '--net', '--network', 'none', img, 'true'],
                stdout=null, stderr=null).returncode == 0:
            self.sg = sg
            return 'singularity'
        sys.exit(f'[work {self.host}] no usable sandbox (wanted {want}); refusing to run untrusted Lean files unsandboxed')

    def stage_deps(self, paths):
        """Copy dependency olean trees (Mathlib etc.) to node-local RAM once; jobs then read them locally."""
        t0 = time.time()
        root = os.path.join(self.a.stage, f'dbuild-deps-{os.getuid()}')
        for i, p in enumerate(paths):
            dst = os.path.join(root, str(i))
            if not os.path.exists(dst + '.ok'):
                shutil.rmtree(dst, ignore_errors=True)
                os.makedirs(root, exist_ok=True)
                subprocess.run(['cp', '-r', '--no-preserve=mode', p, dst], check=True)
                open(dst + '.ok', 'w').close()
            self.stage[p] = dst
        print(f'[work {self.host}] staged {len(paths)} dependency trees to {root} in {time.time() - t0:.0f}s', flush=True)

    def wrap(self, job, tmp):
        argv = [x.replace('@TMP@', tmp) for x in job['argv']]
        binds = [(p, p) for p in job.get('ro', []) if p not in self.stage]
        if self.stage:
            # staged copies appear inside the sandbox as /deps/<i> (binding under /dev/shm is not possible in singularity)
            inside = {p: (f'/deps/{os.path.basename(d)}' if self.sandbox == 'singularity' else d) for p, d in self.stage.items()}
            job['env']['LEAN_PATH'] = ':'.join(inside.get(p, p) for p in job['env']['LEAN_PATH'].split(':'))
            binds += [(d, inside[p]) for p, d in self.stage.items()]
        if self.sandbox == 'singularity':
            sg = [self.sg, 'exec', '--containall', '--no-home', '--cleanenv', '--no-mount', 'bind-paths',
                  '--net', '--network', 'none']
            for src, dst in binds:
                if os.path.exists(src):
                    sg += ['--bind', f'{src}:{dst}:ro']
            sg += ['--bind', f'{tmp}:{tmp}', '--pwd', job.get('cwd', '/'), self.a.image]
            for k, v in list(job.get('env', {}).items()):
                job['env']['SINGULARITYENV_' + k] = v
                job['env']['APPTAINERENV_' + k] = v
            return sg + self.timed(argv, inside_image=True)
        if self.sandbox != 'bwrap':
            return self.timed(argv)
        home = os.path.expanduser('~')
        bw = ['bwrap', '--unshare-net', '--unshare-ipc', '--unshare-pid', '--die-with-parent', '--new-session',
              '--ro-bind', '/', '/', '--dev', '/dev', '--proc', '/proc', '--tmpfs', '/tmp',
              ]
        # hide every shared filesystem and home; only the job's inputs come back, read-only
        for d in ('/scratch', '/project', '/projappl', '/users', '/home', '/bulk', '/flash', '/pfs', '/appl', '/root', '/mnt', '/media', '/var/tmp'):
            if os.path.isdir(d) and not os.path.islink(d):
                bw += ['--tmpfs', d]
        for src, dst in binds:
            if os.path.exists(src):
                bw += ['--ro-bind', src, dst]
        bw += ['--bind', tmp, tmp, '--chdir', job.get('cwd', '/')]
        return bw + self.timed(argv)

    @staticmethod
    def timed(argv, inside_image=False):
        if os.path.exists('/usr/bin/time') and not inside_image:
            return ['/usr/bin/time', '-f', '@@RU %U %S %M', '--'] + argv
        return ['/bin/bash', '-c', '"$@"; rc=$?; times > /tmp/.t; echo "@@TIMES $(tail -n 1 /tmp/.t)"; exit $rc', 'x'] + argv

    def run_job(self, sock, job):
        tmp = os.path.join(self.tmp_root, str(job['id']))
        os.makedirs(tmp, exist_ok=True)
        t0 = time.time()
        r = {'t': 'done', 'id': job['id'], 'mod': job['mod']}
        try:
            for name, content in job.get('files', {}).items():
                with open(os.path.join(tmp, name), 'w') as f:
                    f.write(content)
            argv = self.wrap(job, tmp)
            env = {'PATH': '/usr/bin:/bin', 'HOME': os.path.expanduser('~'), 'LANG': 'C.UTF-8',
                   'SINGULARITYENV_LANG': 'C.UTF-8'}
            env.update(job.get('env', {}))
            p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env,
                                 cwd='/', start_new_session=True)
            with self.plock:
                self.procs[job['id']] = p
            timed_out = []

            def kill():
                timed_out.append(1)
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except OSError:
                    pass
            timer = threading.Timer(job.get('timeout', 14400), kill)
            timer.start()
            out = p.stdout.read()
            _, status, ru = os.wait4(p.pid, 0)
            timer.cancel()
            p.returncode = os.WEXITSTATUS(status) if os.WIFEXITED(status) else -os.WTERMSIG(status)
            r['rc'] = p.returncode
            r['cpu'] = round(ru.ru_utime + ru.ru_stime, 2)
            r['rss'] = ru.ru_maxrss >> 10            # MB (largest single process)
            if timed_out:
                r['timeout'] = True
            text = out.decode('utf-8', 'replace')
            mm = re.search(r'^@@RU ([\d.]+) ([\d.]+) (\d+)\s*$', text, re.M)
            if mm:
                r['cpu'] = round(float(mm.group(1)) + float(mm.group(2)), 2)
                r['rss'] = int(mm.group(3)) >> 10
                text = text[:mm.start()] + text[mm.end():]
            mm = re.search(r'^@@TIMES (\d+)m([\d.,]+)s (\d+)m([\d.,]+)s\s*$', text, re.M)
            if mm:
                r['cpu'] = round(int(mm.group(1)) * 60 + float(mm.group(2).replace(',', '.')) +
                                 int(mm.group(3)) * 60 + float(mm.group(4).replace(',', '.')), 2)
                text = text[:mm.start()] + text[mm.end():]
            text = '\n'.join(l for l in text.splitlines() if not l.startswith('Command exited with non-zero status')
                             and not l.startswith('Command terminated by signal'))
            r['out'] = filter_output(text)[-20000:]
            if r['rc'] == 0:
                for name, final in job.get('moves', []):
                    os.makedirs(os.path.dirname(final), exist_ok=True)
                    shutil.move(os.path.join(tmp, name), final + '.part')
                    os.replace(final + '.part', final)
            with self.plock:
                self.procs.pop(job['id'], None)
                if job['id'] in self.oomed or (r['rc'] in (-9, 137) and not timed_out):
                    r['oom'] = True
        except Exception as e:                # noqa: BLE001 - report anything to the coordinator
            r.update(rc=-1, out=f'worker error: {e!r}')
            with self.plock:
                self.procs.pop(job['id'], None)
        r['wall'] = round(time.time() - t0, 2)
        r.setdefault('cpu', r['wall'])
        shutil.rmtree(tmp, ignore_errors=True)
        try:
            send(sock, self.lock, r)
        except OSError:
            pass

    def mem_guard(self):
        """Kill the fattest job when the node is nearly out of memory, before the kernel/Slurm kills the step."""
        page = os.sysconf('SC_PAGE_SIZE')
        while True:
            time.sleep(2)
            try:
                mi = dict((l.split(':')[0], int(l.split()[1])) for l in open('/proc/meminfo'))
                avail, total = mi['MemAvailable'], mi['MemTotal']
                lim = self.cgroup_headroom()
                if lim is not None:
                    avail = min(avail, lim // 1024)
            except Exception:                 # noqa: BLE001
                continue
            if avail > max(total * 0.04, 2 * 1024 * 1024) and (lim is None or lim > 2 << 30):
                continue
            with self.plock:
                best, best_rss = None, 0
                for jid, p in self.procs.items():
                    rss = tree_rss(p.pid) * page
                    if rss > best_rss:
                        best, best_rss = jid, rss
                if best is not None:
                    self.oomed.add(best)
                    try:
                        os.killpg(self.procs[best].pid, signal.SIGKILL)
                    except OSError:
                        pass
                    print(f'[work {self.host}] memory guard killed job {best} rss={best_rss >> 20}M avail={avail >> 10}M', flush=True)
            time.sleep(3)

    @staticmethod
    def cgroup_headroom():
        try:
            cg = open('/proc/self/cgroup').read().strip().split('::')[-1]
            d = '/sys/fs/cgroup' + cg
            while d.startswith('/sys/fs/cgroup'):
                mx = os.path.join(d, 'memory.max')
                if os.path.exists(mx):
                    v = open(mx).read().strip()
                    if v != 'max':
                        st = dict(l.split() for l in open(os.path.join(d, 'memory.stat')))
                        cur = int(open(os.path.join(d, 'memory.current')).read())
                        reclaimable = int(st.get('inactive_file', 0)) + int(st.get('active_file', 0))
                        return int(v) - (cur - reclaimable)
                d = os.path.dirname(d)
        except Exception:                     # noqa: BLE001
            pass
        return None

    def run(self):
        addr_file = os.path.join(self.a.state, 'coord.addr')
        for _ in range(600):
            if os.path.exists(addr_file):
                break
            time.sleep(1)
        host, port = open(addr_file).read().strip().rsplit(':', 1)
        sock = socket.create_connection((host, int(port)))
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        mem = os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES') >> 30
        send(sock, self.lock, {'t': 'hello', 'host': self.host, 'slots': self.slots, 'mem_gb': mem, 'sandbox': self.sandbox})
        threading.Thread(target=self.mem_guard, daemon=True).start()
        buf = b''
        try:
            while True:
                data = sock.recv(1 << 20)
                if not data:
                    break
                buf += data
                while b'\n' in buf:
                    line, buf = buf.split(b'\n', 1)
                    msg = json.loads(line)
                    if msg['t'] == 'quit':
                        return
                    if msg['t'] == 'conf':
                        if self.a.stage:
                            self.stage_deps(msg['lean_path'])
                        send(sock, self.lock, {'t': 'ready'})
                        continue
                    threading.Thread(target=self.run_job, args=(sock, msg), daemon=True).start()
        finally:
            with self.plock:
                for p in self.procs.values():
                    try:
                        os.killpg(p.pid, signal.SIGKILL)
                    except OSError:
                        pass
            shutil.rmtree(self.tmp_root, ignore_errors=True)


def filter_output(text):
    """Keep errors in full; collapse lean --json warnings/infos to a count."""
    keep, nwarn = [], 0
    for line in text.splitlines():
        if line.startswith('{'):
            try:
                msg = json.loads(line)
                if msg.get('severity') == 'error':
                    keep.append(f"{msg.get('fileName', '')}:{msg.get('pos', {}).get('line')}: error: {msg.get('data', '')[:3000]}")
                else:
                    nwarn += 1
                continue
            except ValueError:
                pass
        keep.append(line)
    if nwarn and keep:
        keep.append(f'({nwarn} warnings/infos dropped)')
    return '\n'.join(keep)


def tree_rss(pid):
    """RSS pages of a process group leader and its descendants (cheap walk of /proc)."""
    total, kids = 0, collections.defaultdict(list)
    for d in os.listdir('/proc'):
        if d.isdigit():
            try:
                f = open(f'/proc/{d}/stat').read().rsplit(')', 1)[1].split()
                kids[int(f[1])].append((int(d), int(f[21])))
            except (OSError, IndexError, ValueError):
                pass
    st = [pid]
    try:
        total += int(open(f'/proc/{pid}/statm').read().split()[1])
    except (OSError, IndexError, ValueError):
        pass
    while st:
        for k, rss in kids.get(st.pop(), []):
            total += rss
            st.append(k)
    return total


# ----------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    c = sub.add_parser('coord')
    c.add_argument('--conf', required=True)
    c.add_argument('--mode', default='build', choices=['build', 'replay'])
    c.add_argument('--roots', default='')
    c.add_argument('--limit', type=int, default=0, help='only run this many currently-ready modules (smoke test)')
    c.add_argument('--port', type=int, default=0)
    c.add_argument('--no-idle-exit', action='store_true')
    w = sub.add_parser('work')
    w.add_argument('--state', required=True)
    w.add_argument('--slots', type=int, default=0)
    w.add_argument('--sandbox', default='auto', choices=['auto', 'bwrap', 'singularity', 'none'])
    w.add_argument('--image', default='', help='singularity image used as the sandbox root')
    w.add_argument('--tmp', default='')
    w.add_argument('--stage', default='', help='node-local dir (e.g. /dev/shm) to copy dependency oleans into')
    a = ap.parse_args()
    if a.cmd == 'coord':
        conf = json.load(open(a.conf))
        co = Coord(conf, a.mode, [r for r in a.roots.split(',') if r], a.limit)
        sys.exit(co.run(a.port, not a.no_idle_exit))
    Worker(a).run()


if __name__ == '__main__':
    main()
