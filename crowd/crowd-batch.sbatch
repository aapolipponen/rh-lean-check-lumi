#!/bin/bash
# Build claimed packets/modules of rohanarun/alpoge-rh-replay one after another with the repo's own tool
# (lake), in a no-network Singularity container.  Mathlib and the lake build dir live on the node's RAM
# disk (Lustre mmap contention makes 256 parallel leans crawl); the build dir is restored from and saved
# to one tar on /flash, so jobs are cumulative.      sbatch crowd-batch.sbatch P1217 P1236 ...
# RH_FULL=1 additionally runs `lake build +Main:olean` (the repo's verify.sh build step) after the list.
#SBATCH --account=project_462001825
#SBATCH --partition=standard
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128
#SBATCH --time=04:00:00
#SBATCH --signal=B:TERM@600
#SBATCH --job-name=rh-crowd
#SBATCH --output=/flash/project_462001825/rieman/logs/%x-%j.out
set -uo pipefail
B=/flash/project_462001825/rieman
REPO=$B/crowd/repo
S=/dev/shm/rh-$SLURM_JOB_ID
TARIN=${RH_TAR_IN:-$B/lake-build.tar}
TAR=${RH_TAR_OUT:-$TARIN}
mkdir -p "$B/receipts" "$B/cache" "$S/build"
echo "start_utc=$(date -u +%FT%TZ) node=$(hostname) cpus=$(nproc) mem_kb=$(grep MemTotal /proc/meminfo | awk '{print $2}') repo_commit=$(git -C $REPO rev-parse HEAD) ids=$*"
manifest() { (cd "$1" && find . -name '*.olean' -print0 | sort -z | xargs -0 -P 32 -n 64 sha256sum | sort -k2 | sha256sum | cut -d' ' -f1); }
t=$(date +%s); cp -r $B/lean/.lake/packages $S/packages; echo "staged packages in $(( $(date +%s) - t ))s"
[ -f $TARIN ] && { t=$(date +%s); tar -xf $TARIN -C $S/build; echo "restored build dir ($(find $S/build -name '*.olean' | wc -l) oleans) in $(( $(date +%s) - t ))s"; }
echo "deps_oleans_sha256_flash=$(manifest $B/lean/.lake/packages) deps_oleans_sha256_staged_before=$(manifest $S/packages)"
save() { t=$(date +%s); tar -cf $TAR.tmp -C $S/build . && mv $TAR.tmp $TAR; echo "saved build dir ($(find $S/build -name '*.olean' | wc -l) oleans, $(du -sh $TAR | cut -f1)) in $(( $(date +%s) - t ))s"; }
trap 'echo "TERM at $(date -u +%FT%TZ): saving"; kill $PID 2>/dev/null; wait $PID 2>/dev/null; save; rm -rf $S; exit 143' TERM
box() { singularity exec --containall --no-home --cleanenv --no-mount bind-paths --net --network none \
  --bind $B/elan:$B/elan:ro --bind $B/lean:$B/lean --bind $B/lean/src:$B/lean/src:ro \
  --bind $S/packages:$B/lean/.lake/packages --bind $S/build:$B/lean/.lake/build \
  --bind $B/cache:$B/cache --bind $REPO:$REPO:ro --bind $B/receipts:$B/receipts \
  --env PATH=$B/elan/bin:/usr/local/bin:/usr/bin:/bin --env LANG=C.UTF-8 --env LD_PRELOAD=$B/rhcheck/rhshim.so \
  --bind $B/rhcheck:$B/rhcheck:ro --env ELAN_HOME=$B/elan --env XDG_CACHE_HOME=$B/cache --pwd $B/lean $B/crowd.sif "$@"; }
fail=0
for ID in "$@"; do
  OUT=$B/receipts/$ID-$SLURM_JOB_ID
  t0=$(date +%s); echo "[$ID] start_utc=$(date -u +%FT%TZ)"
  box python3 $REPO/tracker/tasks.py build "$ID" $B/lean "$OUT" --fast-bundle & PID=$!; wait $PID; rc=$?
  echo "[$ID] end_utc=$(date -u +%FT%TZ) elapsed_s=$(( $(date +%s) - t0 )) exit=$rc built_lines=$(grep -cE '^✔' $OUT/build.log 2>/dev/null)"
  [ $rc -ne 0 ] && { fail=1; grep -E '^✖|error' $OUT/build.log | head -5 | cut -c1-300; }
done
if [ "${RH_FULL:-0}" = 1 ]; then
  save
  LOG=$B/receipts/lake-full-$SLURM_JOB_ID.log; t0=$(date +%s); echo "[full] start_utc=$(date -u +%FT%TZ)"
  box bash -c "elan run leanprover/lean4:v4.33.1 lake build +Main:olean > $LOG 2>&1" & PID=$!; wait $PID; rc=$?
  echo "[full] end_utc=$(date -u +%FT%TZ) elapsed_s=$(( $(date +%s) - t0 )) exit=$rc"; tail -n 3 $LOG | cut -c1-300
  [ $rc -eq 0 ] && echo REPLAY_SOURCE_BUILD_PASSED || fail=1
fi
echo "deps_oleans_sha256_staged_after=$(manifest $S/packages)"
save; rm -rf $S
echo "end_utc=$(date -u +%FT%TZ) fail=$fail"
exit $fail
