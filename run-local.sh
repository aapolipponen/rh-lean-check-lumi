#!/bin/bash
# run-local.sh BASE [coord args...]  -- single node: coordinator + one worker (SLOTS env, default all cpus)
BASE=$(realpath "$1"); shift
HERE=$(dirname "$(realpath "$0")")
mkdir -p "$BASE/tmp" "$BASE/state"
rm -f "$BASE/state/coord.addr"
python3 "$HERE/dbuild.py" coord --conf "$BASE/conf.json" "$@" &
C=$!
python3 "$HERE/dbuild.py" work --state "$BASE/state" --slots "${SLOTS:-0}" --sandbox "${SANDBOX:-auto}" --image "${IMAGE:-}" --tmp "${WTMP:-$BASE/tmp}"
wait $C
