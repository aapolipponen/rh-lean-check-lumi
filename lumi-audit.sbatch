#!/bin/bash
# Independent audit of the five Main theorems from the compiled tree (verify/Audit.lean), no network.
#SBATCH --account=project_462001825
#SBATCH --partition=standard
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128
#SBATCH --time=04:00:00
#SBATCH --job-name=rh-audit
#SBATCH --output=/flash/project_462001825/rieman/logs/%x-%j.out
set -uo pipefail
B=$(realpath /flash/project_462001825/rieman)
OUT=${RH_VERIFY_OUT:-$B/verify}
F=/flash/project_462001825/rieman   # conf.json may spell paths through this symlink
mkdir -p $B/verify $OUT
echo "start_utc=$(date -u +%FT%TZ) node=$(hostname)"
cat $B/state/summary-build.json 2>/dev/null | head -c 600; echo
singularity exec --containall --no-home --cleanenv --no-mount bind-paths --net --network none \
  --bind $B/elan:$B/elan:ro --bind $B/lean:$B/lean:ro --bind $B/build:$B/build:ro --bind $B/rhcheck:$B/rhcheck:ro \
  --bind $B/elan:$F/elan:ro --bind $B/lean:$F/lean:ro --bind $B/build:$F/build:ro \
  --bind $B/conf.json:$B/conf.json:ro --bind $B/verify:$B/verify --bind $OUT:$OUT --env RH_VERIFY_OUT=$OUT \
  --env LANG=C.UTF-8 --env LEAN_NUM_THREADS=${RH_THREADS:-96} --env LD_PRELOAD=$B/rhcheck/rhshim.so --env RH_MIN_MAP=1048576 $B/crowd.sif $B/rhcheck/verify/audit.sh $B ${1:-Main} "${@:2}" 2>&1 | cut -c1-6000
rc=${PIPESTATUS[0]}
echo "end_utc=$(date -u +%FT%TZ) exit=$rc"
exit $rc
