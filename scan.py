#!/usr/bin/env python3
"""Scan a Lean source tree: import graph + static audit of trust-relevant constructs.

usage: scan.py SRC_DIR OUT_DIR [--jobs N]
writes OUT_DIR/graph.json   {module: {"size": bytes, "imports": [...], "ext": [...]}}
       OUT_DIR/audit.json   {pattern: {"count": n, "files": {module: n}}}, set_option histogram
       OUT_DIR/scan.txt     human summary
Reads files only; never executes anything from the tree.
"""
import json, os, re, sys, collections
from multiprocessing import Pool

IMPORT_RE = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s]+)\s*$')
BLOCK_COMMENT = re.compile(r'/-.*?-/', re.S)

# name -> regex, applied to source with comments and string literals stripped
AUDIT = {
    'axiom':            r'(?<![\w.#])axiom\s',
    'sorry':            r'(?<![\w.])sorry(?![\w.\'])',
    'admit':            r'(?<![\w.])admit(?![\w.\'])',
    'native_decide':    r'native_decide',
    'ofReduceBool':     r'ofReduceBool|reduceBool|reduceNat|trustCompiler',
    'bv_decide':        r'(?<![\w.])bv_decide',
    'implemented_by':   r'implemented_by',
    'extern':           r'@\[\s*extern|(?<![\w.])extern\s+"',
    'csimp':            r'@\[\s*csimp',
    'unsafe':           r'(?<![\w.])unsafe\s',
    'partial':          r'(?<![\w.])partial\s+def',
    'opaque':           r'(?<![\w.])opaque\s',
    'run_cmd':          r'(?<![\w.])run_cmd\b|(?<![\w.])run_elab\b|(?<![\w.])run_meta\b',
    'hash_eval':        r'#eval',
    'initialize':       r'(?<![\w.])(?:builtin_)?initialize\b',
    'elab':             r'(?<![\w.])(?:local\s+|scoped\s+)?elab(?:_rules)?\b',
    'macro':            r'(?<![\w.])(?:local\s+|scoped\s+)?macro(?:_rules)?\b',
    'syntax':           r'(?<![\w.])(?:local\s+|scoped\s+)?syntax\b|declare_syntax_cat',
    'notation':         r'(?<![\w.])(?:local\s+|scoped\s+)?(?:notation|infixl?|infixr|prefix|postfix)\b',
    'env_hack':         r'modifyEnv|setEnv|addDecl|addAndCompile|Environment\.add|mkDefinitionValEx|Kernel\.|withoutModifyingEnv|registerBuiltin',
    'debug_option':     r'debug\.|skipKernelTC|kernel\.',
    'open_Lean':        r'(?<![\w.])open\s[^\n]*\bLean\b',
    'IO':               r'(?<![\w.])IO\.|IO\.Process|IO\.FS|System\.FilePath|readFile|writeFile|\bspawn\b',
    'attr_instance':    r'attribute\s*\[[^\]]*instance',
    'local_instance':   r'local\s+instance',
    'simproc':          r'(?<![\w.])(?:d?simproc)(?:_decl)?\b',
    'unseal_irreducible': r'(?<![\w.])unseal\b|attribute\s*\[[^\]]*(?:reducible|irreducible)',
    'decide_tac':       r'(?<![\w.])decide(?![\w.\'])',
    'nolint_etc':       r'set_option\s+linter',
}
AUDIT_C = {k: re.compile(v) for k, v in AUDIT.items()}
SETOPT = re.compile(r'set_option\s+([\w.]+)\s+(\S+)')
STRING = re.compile(r'"(?:\\.|[^"\\])*"')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|instance|abbrev|structure|class|inductive|example)\b', re.M)


def strip_comments(s):
    # nested block comments are rare; iterate until stable
    prev = None
    while prev != s:
        prev = s
        s = BLOCK_COMMENT.sub(' ', s)
    s = re.sub(r'--[^\n]*', '', s)
    return s


def scan_file(args):
    src, rel = args
    path = os.path.join(src, rel)
    mod = rel[:-5].replace('/', '.')
    try:
        raw = open(path, 'rb').read()
    except OSError as e:
        return mod, {'error': str(e)}
    size = len(raw)
    text = raw.decode('utf-8', 'replace')
    code = strip_comments(text)
    imports, is_module, prelude = [], False, False
    for line in code.split('\n'):
        t = line.strip()
        if not t:
            continue
        if t == 'module':
            is_module = True
            continue
        if t == 'prelude':
            prelude = True
            continue
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))
            continue
        # several imports on one line?
        if t.startswith('import ') or ' import ' in t.split('--')[0][:40]:
            toks = t.split()
            ok = True
            for i, tok in enumerate(toks):
                if tok == 'import' and i + 1 < len(toks):
                    nxt = toks[i + 1]
                    if nxt == 'all' and i + 2 < len(toks):
                        nxt = toks[i + 2]
                    imports.append(nxt)
                elif tok not in ('public', 'private', 'meta', 'all', 'import') and (i == 0 or toks[i - 1] not in ('import', 'all')):
                    ok = False
            if ok:
                continue
        break
    nostr = STRING.sub('""', code)
    hits = {}
    for k, rx in AUDIT_C.items():
        n = len(rx.findall(nostr))
        if n:
            hits[k] = n
    opts = collections.Counter(f'{a} {b}' for a, b in SETOPT.findall(nostr))
    decls = collections.Counter(DECL.findall(nostr))
    return mod, {'size': size, 'lines': text.count('\n'), 'imports': imports, 'module_kw': is_module,
                 'prelude': prelude, 'hits': hits, 'opts': dict(opts), 'decls': dict(decls)}


def main():
    src, out = sys.argv[1], sys.argv[2]
    jobs = int(sys.argv[sys.argv.index('--jobs') + 1]) if '--jobs' in sys.argv else 8
    os.makedirs(out, exist_ok=True)
    rels = []
    for d, _, fs in os.walk(src):
        for f in fs:
            p = os.path.relpath(os.path.join(d, f), src)
            if f.endswith('.lean'):
                rels.append(p)
            else:
                print('NON-LEAN FILE', p)
    rels.sort()
    with Pool(jobs) as pool:
        res = dict(pool.imap_unordered(scan_file, [(src, r) for r in rels], chunksize=500))
    mods = set(res)
    graph, audit, opts, decls = {}, collections.defaultdict(dict), collections.Counter(), collections.Counter()
    ext = collections.Counter()
    for m, r in res.items():
        if 'error' in r:
            print('ERROR', m, r['error'])
            continue
        internal = [i for i in r['imports'] if i in mods]
        external = [i for i in r['imports'] if i not in mods]
        for e in external:
            ext[e] += 1
        graph[m] = {'size': r['size'], 'lines': r['lines'], 'imports': internal, 'ext': external}
        if r['module_kw']:
            audit['module_keyword'][m] = 1
        if r['prelude']:
            audit['prelude'][m] = 1
        for k, n in r['hits'].items():
            audit[k][m] = n
        opts.update(r['opts'])
        decls.update(r['decls'])
    json.dump(graph, open(os.path.join(out, 'graph.json'), 'w'))
    json.dump({'patterns': audit, 'set_option': dict(opts), 'decls': dict(decls), 'external_imports': dict(ext)},
              open(os.path.join(out, 'audit.json'), 'w'))

    # ---- graph stats
    order, indeg = [], {m: 0 for m in graph}
    rev = collections.defaultdict(list)
    for m, g in graph.items():
        for i in g['imports']:
            rev[i].append(m)
            indeg[m] += 1
    q = collections.deque(m for m, d in indeg.items() if d == 0)
    while q:
        m = q.popleft()
        order.append(m)
        for d in rev[m]:
            indeg[d] -= 1
            if indeg[d] == 0:
                q.append(d)
    cyc = len(graph) - len(order)
    level, wdepth = {}, {}
    for m in order:
        imps = graph[m]['imports']
        level[m] = 1 + max((level[i] for i in imps), default=0)
        wdepth[m] = graph[m]['size'] + max((wdepth[i] for i in imps), default=0)

    def closure(roots):
        seen, st = set(), [r for r in roots if r in graph]
        while st:
            m = st.pop()
            if m in seen:
                continue
            seen.add(m)
            st.extend(graph[m]['imports'])
        return seen

    main_cl = closure(['Main', 'Statements'])
    tot = sum(g['size'] for g in graph.values())
    L = []
    P = L.append
    P(f'modules: {len(graph)}   bytes: {tot}   lines: {sum(g["lines"] for g in graph.values())}')
    P(f'import edges: {sum(len(g["imports"]) for g in graph.values())}   cycles(unsorted modules): {cyc}')
    P(f'Main closure: {len(main_cl)} modules, {sum(graph[m]["size"] for m in main_cl)} bytes '
      f'({100 * len(main_cl) / max(1, len(graph)):.1f}% of modules)')
    P(f'not reachable from Main: {len(graph) - len(main_cl)} modules')
    if level:
        P(f'max import depth (levels): {max(level.values())}   in Main closure: {max((level[m] for m in main_cl), default=0)}')
        wm = max(wdepth, key=wdepth.get)
        P(f'heaviest chain by source bytes: {wdepth[wm]} bytes ending at {wm} '
          f'({100 * wdepth[wm] / tot:.2f}% of all bytes => parallel speedup bound ~{tot / wdepth[wm]:.0f}x if time~bytes)')
        widths = collections.Counter(level.values())
        P('level widths (level:count): ' + ' '.join(f'{k}:{widths[k]}' for k in sorted(widths)[:60]) + (' ...' if len(widths) > 60 else ''))
    top = collections.Counter()
    for m, g in graph.items():
        top[m.split('.')[0]] += 1
    P('top-level: ' + ', '.join(f'{k}={v}' for k, v in top.most_common()))
    P('external imports: ' + ', '.join(f'{k}={v}' for k, v in ext.most_common(40)))
    P('no-import files: ' + str(sum(1 for g in graph.values() if not g['imports'] and not g['ext'])))
    P('decl keywords: ' + ', '.join(f'{k}={v}' for k, v in decls.most_common()))
    P('')
    P('AUDIT (pattern: total hits / files; in Main closure: files) -- comments and strings stripped')
    for k in sorted(audit, key=lambda k: sum(audit[k].values())):
        fs = audit[k]
        inm = [m for m in fs if m in main_cl]
        P(f'  {k:20s} {sum(fs.values()):8d} hits {len(fs):7d} files   main-closure files: {len(inm)}')
        if len(fs) <= 12:
            for m in sorted(fs):
                P(f'      {m} x{fs[m]}')
    P('')
    P('set_option histogram:')
    for k, v in opts.most_common(60):
        P(f'  {v:8d}  {k}')
    open(os.path.join(out, 'scan.txt'), 'w').write('\n'.join(L) + '\n')
    print('\n'.join(L))


if __name__ == '__main__':
    main()
