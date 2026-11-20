#!/usr/bin/env python3
"""used_report.py GRAPH USED_MODULES.txt [OUT.md] -- how much of the tree the main theorems actually depend on.

USED_MODULES.txt comes from Audit.lean: one "module constant-count" line for every module that contributes
at least one constant to the proof terms or statements of the audited theorems (transitively).
A module can be imported everywhere and still be unused in this sense."""
import json, sys, collections
g = json.load(open(sys.argv[1]))
used = {}
for line in open(sys.argv[2]):
    p = line.split()
    if len(p) == 2:
        used[p[0]] = int(p[1])
proj = {m: c for m, c in used.items() if m in g}
dep = {m: c for m, c in used.items() if m not in g}
L = []
P = L.append
tot_lines = sum(v['lines'] for v in g.values())
P(f'Project modules that contribute at least one constant to the five `Main` theorems: '
  f'**{len(proj):,} of {len(g):,}** ({100 * len(proj) / len(g):.1f}%), '
  f'holding {sum(g[m]["lines"] for m in proj):,} of {tot_lines:,} source lines '
  f'({100 * sum(g[m]["lines"] for m in proj) / tot_lines:.1f}%).')
P(f'Constants reached: {sum(proj.values()):,} in the project, {sum(dep.values()):,} in Mathlib and other dependencies '
  f'({len(dep):,} dependency modules).')
P('')
for depth in (1, 2):
    agg = collections.defaultdict(lambda: [0, 0, 0, 0])
    for m, v in g.items():
        k = '.'.join(m.split('.')[:depth])
        a = agg[k]
        a[0] += 1
        a[2] += v['lines']
        if m in proj:
            a[1] += 1
            a[3] += v['lines']
    P(f'| {"Library" if depth == 1 else "Directory"} | modules | used | used % | lines | used lines % |')
    P('|---|---:|---:|---:|---:|---:|')
    rows = sorted(agg.items(), key=lambda kv: -kv[1][0])
    for k, a in rows[:60 if depth == 2 else 20]:
        P(f'| `{k}` | {a[0]:,} | {a[1]:,} | {100 * a[1] / a[0]:.0f}% | {a[2]:,} | {100 * a[3] / max(1, a[2]):.0f}% |')
    P('')
unused_dirs = collections.Counter()
alld = collections.Counter()
for m in g:
    k = '.'.join(m.split('.')[:3])
    alld[k] += 1
    if m not in proj:
        unused_dirs[k] += 1
dead = sorted((k for k in alld if unused_dirs[k] == alld[k] and alld[k] >= 20), key=lambda k: -alld[k])
P(f'Directories (depth 3, at least 20 modules) with no used module at all: {len(dead)}')
for k in dead[:40]:
    P(f'- `{k}` ({alld[k]:,} modules)')
text = '\n'.join(L) + '\n'
if len(sys.argv) > 3:
    open(sys.argv[3], 'w').write(text)
print(text)
