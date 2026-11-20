#!/bin/bash
# mkconf.sh BASE > conf.json   (BASE holds lean/ (project), out/graph.json; toolchain found via elan)
set -euo pipefail
BASE=$(realpath "$1")
TC=$(cat "$BASE/lean/lean-toolchain" | sed 's#/#--#; s#:#---#')
LEANBIN="${ELAN_HOME:-$HOME/.elan}/toolchains/$TC/bin"
[ -x "$LEANBIN/lean" ] || { echo "no lean at $LEANBIN" >&2; exit 1; }
python3 - "$BASE" "$LEANBIN" <<'PY'
import json, os, sys, glob
base, leanbin = sys.argv[1], sys.argv[2]
man = json.load(open(f'{base}/lean/lake-manifest.json'))
lp = [f'{base}/lean/.lake/packages/{p["name"]}/.lake/build/lib/lean' for p in man['packages']]
lp = [p for p in lp if os.path.isdir(p)]
assert any('mathlib' in p for p in lp), 'mathlib oleans missing: run lake exe cache get'
print(json.dumps({
    'graph': f'{base}/out/graph.json', 'src': f'{base}/lean/src', 'out': f'{base}/build', 'state': f'{base}/state',
    'lean': leanbin, 'lean_path': lp, 'package': 'tree',
    'args': ['--tstack=400000'],
    # lakefile.toml [leanOptions]
    'options': {'autoImplicit': False, 'relaxedAutoImplicit': False, 'maxSynthPendingDepth': 3,
                'pp.unicode.fun': True, 'maxHeartbeats': 4000000},
    # lean_lib GroundTheoryFields
    'lib_opts': {'GroundTheory.LocalFields.': {'synthInstance.maxHeartbeats': 400000},
                 'GroundTheory.GlobalFields.': {'synthInstance.maxHeartbeats': 400000}},
    'threads': 1, 'timeout': 14400,
    'preload': f'{base}/rhcheck/rhshim.so' if os.path.exists(f'{base}/rhcheck/rhshim.so') else '',
    'closure': f'{base}/out/closure.tsv'}, indent=1))
PY
