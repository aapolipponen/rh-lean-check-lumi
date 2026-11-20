#!/bin/bash
# Whole-tree build with the replay repo's own method (lake build +Main:olean, as in its verify.sh),
# in the same volume the packet receipts use, inside a no-network Singularity container.
# Resumable: lake skips what is already built.   sbatch crowd-full.sbatch
#SBATCH --account=project_462001825
#SBATCH --partition=standard
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128
#SBATCH --time=12:00:00
#SBATCH --job-name=rh-lake
#SBATCH --output=/flash/project_462001825/rieman/logs/%x-%j.out
set -uo pipefail
B=/flash/project_462001825/rieman
REPO=$B/crowd/repo
mkdir -p "$B/cache" "$B/receipts"
LOG=$B/receipts/lake-full-$SLURM_JOB_ID.log
echo "start_utc=$(date -u +%FT%TZ) node=$(hostname) cpus=$(nproc) repo_commit=$(git -C $REPO rev-parse HEAD)"
t0=$(date +%s)
singularity exec --containall --no-home --cleanenv --no-mount bind-paths --net --network none \
  --bind $B/elan:$B/elan:ro --bind $B/lean:$B/lean --bind $B/lean/src:$B/lean/src:ro \
  --bind $B/cache:$B/cache --bind $REPO:$REPO:ro --bind $B/receipts:$B/receipts \
  --env PATH=$B/elan/bin:/usr/local/bin:/usr/bin:/bin --env LANG=C.UTF-8 \
  --env ELAN_HOME=$B/elan --env XDG_CACHE_HOME=$B/cache --pwd $B/lean \
  $B/crowd.sif bash -c "elan run leanprover/lean4:v4.33.1 lake build +Main:olean > $LOG 2>&1"
rc=$?
echo "end_utc=$(date -u +%FT%TZ) elapsed_s=$(( $(date +%s) - t0 )) exit=$rc"
grep -cE '^✔' $LOG; grep -E '^✖|^error' $LOG | head -20; tail -3 $LOG
[ $rc -eq 0 ] && echo REPLAY_SOURCE_BUILD_PASSED
exit $rc
