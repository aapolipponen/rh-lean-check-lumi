#!/usr/bin/env python3
"""stats.py BASE [mode] -- cost model from results so far, extrapolated to the whole tree."""
import json, sys, collections
base = sys.argv[1]; mode = sys.argv[2] if len(sys.argv) > 2 else 'build'
g = json.load(open(f'{base}/out/graph.json'))
rs = [json.loads(l) for l in open(f'{base}/state/results-{mode}.jsonl')]
ok = {r['mod']: r for r in rs if r['rc'] == 0 and r['mod'] in g}
bad = [r for r in rs if r['rc'] != 0]
# transitive import counts are expensive; use level (longest import chain) as the depth measure
level = {}
def lv(m):
    st = [m]
    while st:
        x = st[-1]
        if x in level: st.pop(); continue
        todo = [i for i in g[x]['imports'] if i not in level]
        if todo: st.extend(todo)
        else:
            level[x] = 1 + max((level[i] for i in g[x]['imports']), default=0); st.pop()
    return level[m]
for m in g: lv(m)
cpu = sum(r['cpu'] for r in ok.values()); by = sum(g[m]['size'] for m in ok)
tot_by = sum(v['size'] for v in g.values())
print(f'ok {len(ok)}/{len(g)}  failed attempts {len(bad)}  cpu {cpu/3600:.1f} h  mean {cpu/max(1,len(ok)):.1f} s/file  {cpu/max(1,by)*1000:.2f} cpu-s/KB')
# fit cpu = a*files + b*bytes roughly by level buckets
buckets = collections.defaultdict(list)
for m, r in ok.items(): buckets[min(level[m] // 20, 10)].append((r['cpu'], g[m]['size'], r['wall'], r.get('rss', 0)))
print('level-bucket  n   mean-cpu  cpu-s/KB  mean-wall  max-cpu  max-rss-MB')
for b in sorted(buckets):
    v = buckets[b]
    print(f'  {b*20:3d}-{b*20+19:3d} {len(v):6d} {sum(x[0] for x in v)/len(v):8.1f} {sum(x[0] for x in v)/sum(x[1] for x in v)*1000:8.2f} '
          f'{sum(x[2] for x in v)/len(v):8.1f} {max(x[0] for x in v):8.0f} {max(x[3] for x in v):8d}')
est = cpu / max(1, by) * tot_by / 3600
print(f'extrapolated total (by bytes): {est:.0f} CPU-hours')
top = sorted(ok.values(), key=lambda r: -r['cpu'])[:8]
for r in top: print(f"  slow: {r['cpu']:.0f}s cpu {r['wall']:.0f}s wall {g[r['mod']]['size']} B  {r['mod']}")
seen = set()
for r in bad:
    if r['mod'] in ok or r['mod'] in seen: continue
    seen.add(r['mod']); print('FAILED', r['mod'], 'rc', r['rc'], (r.get('out') or '')[:700].replace('\n', ' | '))
print('distinct failed modules:', len(seen))
