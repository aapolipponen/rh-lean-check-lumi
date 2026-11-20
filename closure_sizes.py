#!/usr/bin/env python3
"""closure_sizes.py GRAPH OUT.tsv -- transitive project-import count per module (bitset DP in topological order)."""
import json, sys, collections
g = json.load(open(sys.argv[1]))
idx = {m: i for i, m in enumerate(g)}
indeg = {m: len(v['imports']) for m, v in g.items()}
rev = collections.defaultdict(list)
for m, v in g.items():
    for i in v['imports']:
        rev[i].append(m)
q = [m for m, d in indeg.items() if d == 0]
left = {m: len(rev[m]) for m in g}           # free a bitset once all dependents consumed it
bits, cnt = {}, {}
while q:
    m = q.pop()
    b = 1 << idx[m]
    for i in g[m]['imports']:
        b |= bits[i]
        left[i] -= 1
        if left[i] == 0:
            del bits[i]
    bits[m] = b
    cnt[m] = bin(b).count('1')
    for d in rev[m]:
        indeg[d] -= 1
        if indeg[d] == 0:
            q.append(d)
with open(sys.argv[2], 'w') as f:
    for m, c in cnt.items():
        f.write(f'{c}\t{m}\n')
cs = sorted(cnt.values())
n = len(cs)
print('modules', n, 'max closure', cs[-1])
for t in (5000, 10000, 12000, 15000, 20000, 30000, 40000, 60000, 80000, 100000, 140000):
    print(f'closure > {t}: {sum(1 for c in cs if c > t)}')
