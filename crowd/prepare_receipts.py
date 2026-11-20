#!/usr/bin/env python3
"""prepare_receipts.py LOCAL_DIR -- fetch finished packet receipts from LUMI and write a ready-to-post
"Replay submission" comment for each claim.  Posts nothing."""
import json, os, re, subprocess, sys, hashlib
out = sys.argv[1]
R = 'lumi:/flash/project_462001825/rieman'
os.makedirs(out, exist_ok=True)
subprocess.run(['rsync', '-a', '--include=P*-*/', '--include=P*-*/*', '--exclude=*', f'{R}/receipts/', out + '/'], check=True)
subprocess.run(['rsync', '-a', '--include=rh-crowd*.out', '--exclude=*', f'{R}/logs/', out + '/slurm/'], check=True)
claims = {}
for line in open(os.path.join(os.path.dirname(out.rstrip('/')), 'claims-status.txt')):
    p = line.split()
    if len(p) >= 3 and 'claim-granted' in p[2]:
        claims[p[1]] = p[0]
slurm = {}
for f in os.listdir(out + '/slurm'):
    txt = open(f'{out}/slurm/{f}').read()
    head = txt.splitlines()[0] if txt else ''
    for m in re.finditer(r'^\[(P\d+)\] start_utc=(\S+)\n(?:.*\n)*?\[\1\] end_utc=(\S+) elapsed_s=(\d+) exit=(\d+)', txt, re.M):
        slurm[m.group(1)] = dict(start=m.group(2), end=m.group(3), elapsed=m.group(4), rc=m.group(5), file=f, head=head,
                                 restored=re.search(r'restored build dir \((\d+) oleans\)', txt))
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as fh:
        for b in iter(lambda: fh.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()
rows = []
for d in sorted(os.listdir(out)):
    m = re.match(r'(P\d+)-(\d+)$', d)
    if not m or not os.path.exists(f'{out}/{d}/receipt.json'):
        continue
    pid, job = m.groups()
    r = json.load(open(f'{out}/{d}/receipt.json'))
    s = slurm.get(pid)
    if r['exit_code'] != 0 or not s or pid == 'P1217':
        continue
    log = open(f'{out}/{d}/build.log', errors='replace').read()
    built = len(re.findall(r'^✔ \[\d+/\d+\] Built ', log, re.M))
    tail = log.strip().splitlines()[-1]
    restored = s['restored'].group(1) if s['restored'] else '0'
    cm = re.search(r'repo_commit=([0-9a-f]+)', s['head'])
    commit = cm.group(1) if cm else 'unknown'
    body = f"""Replay submission

**Task:** {pid} ({len(r['tasks'])} modules). **Exit status:** {r['exit_code']}. **Elapsed:** {s['elapsed']} s for the `tasks.py build` step ({s['start']} to {s['end']}).

**What ran:** `python3 tracker/tasks.py build {pid} <volume>/lean <receipt> --fast-bundle` at replay-repo commit `{commit}`, on one LUMI-C node (2x EPYC 7763, 256 hardware threads, 251 GB), inside a Singularity container with no network. The Lake build directory started from the {restored} project oleans of my earlier P1217 build (claim #732, same volume and inputs) and is shared with the other packets built in the same job, so Lake compiled only what was missing: {built} modules were built locally in this step ("{tail}"). No infrastructure retries.

**Inputs:** the 14 parts from alpo.ge match `parts.sha256`; Lean 4.33.1 (commit 819816b2); Mathlib `{r['mathlib']}` from `lake exe cache get`. The volume is laid out as `verify.sh --prepare-only` does but was prepared by hand, not by running `verify.sh`. The dependency oleans were fingerprinted before and after the job and did not change.

**Artifacts** (RELEASE_URL):
- `receipt.json` sha256 `{sha(f'{out}/{d}/receipt.json')}`
- `build.log` sha256 `{r['log_sha256']}`
- `targets.tar.gz` sha256 `{r.get('bundle_sha256', 'n/a')}`
- `{s['file']}` (UTC times, node, dependency fingerprints)

This is a compiler pass for these targets only. No kernel replay and no axiom audit were run as part of this submission.
"""
    assert sha(f'{out}/{d}/build.log') == r['log_sha256'], pid
    open(f'{out}/{d}/comment.md', 'w').write(body)
    rows.append((pid, claims.get(pid, '?'), d, s['elapsed'], built))
with open(out + '/READY.tsv', 'w') as f:
    for row in rows:
        f.write('\t'.join(map(str, row)) + '\n')
        print(*row)
print(len(rows), 'receipts ready; not posted')
