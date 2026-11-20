#!/bin/bash
# audit.sh BASE [ROOT] -- run the independent audit against the built tree (after the build finished)
set -euo pipefail
BASE=$(realpath "$1"); ROOT=${2:-Main}
HERE=$(dirname "$(realpath "$0")")
LEANBIN=$(python3 -c "import json;print(json.load(open('$BASE/conf.json'))['lean'])")
LP=$(python3 -c "import json;c=json.load(open('$BASE/conf.json'));print(':'.join(c['lean_path']+[c['out']+'/lib']))")
OUT=${RH_VERIFY_OUT:-$BASE/verify}
mkdir -p "$OUT"
shift; shift || true
PAIRS=("$@")
[ ${#PAIRS[@]} -gt 0 ] || PAIRS=(riemannHypothesis=RiemannHypothesis riemannZeta_eq_zero_re=RiemannZetaZerosOnLine \
  LFunction_ne_zero_of_half_lt_re=DirichletLNonvanishingRightOfHalf LFunction_eq_zero_re=DirichletLZerosOnLine \
  LFunction_eq_zero_re_of_isPrimitive=PrimitiveDirichletLZerosOnLine)
cd "$OUT"
PATH="$LEANBIN:$PATH" LEAN_PATH="$LP" "$LEANBIN/lean" --run "$HERE/Audit.lean" "$OUT" "$ROOT" "${PAIRS[@]}"
