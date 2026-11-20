#!/bin/bash
# Build one claimed packet/module of rohanarun/alpoge-rh-replay with the repo's own tool (lake),
# inside a no-network Singularity container.   sbatch crowd-build.sbatch P1217
#SBATCH --account=project_462001825
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128
#SBATCH --mem=200G
#SBATCH --time=00:30:00
#SBATCH --job-name=rh-crowd
#SBATCH --output=/flash/project_462001825/rieman/logs/%x-%j.out
set -uo pipefail
ID=$1
B=/flash/project_462001825/rieman
REPO=$B/crowd/repo
OUT=$B/receipts/$ID-$SLURM_JOB_ID
mkdir -p "$B/receipts" "$B/cache" "$B/lean/.lake/build"
echo "start_utc=$(date -u +%FT%TZ) node=$(hostname) cpus=$(nproc) mem_kb=$(grep MemTotal /proc/meminfo | awk '{print $2}') repo_commit=$(git -C $REPO rev-parse HEAD)"
# lake insists on writing hash files into .lake/packages, so it stays writable; fingerprint the dependency
# oleans before and after to show the untrusted build did not alter them
manifest() { (cd $B/lean/.lake/packages && find . -name '*.olean' -print0 | sort -z | xargs -0 -P 32 -n 64 sha256sum | sort -k2 | sha256sum | cut -d' ' -f1); }
DEPS_BEFORE=$(manifest); echo "deps_oleans_sha256_before=$DEPS_BEFORE"
t0=$(date +%s)
singularity exec --containall --no-home --cleanenv --no-mount bind-paths --net --network none \
  --bind $B/elan:$B/elan:ro --bind $B/lean:$B/lean --bind $B/lean/src:$B/lean/src:ro \
  --bind $B/cache:$B/cache --bind $REPO:$REPO:ro --bind $B/receipts:$B/receipts \
  --env PATH=$B/elan/bin:/usr/local/bin:/usr/bin:/bin --env LANG=C.UTF-8 \
  $B/crowd.sif python3 $REPO/tracker/tasks.py build "$ID" $B/lean "$OUT" --bundle
rc=$?
echo "end_utc=$(date -u +%FT%TZ) elapsed_s=$(( $(date +%s) - t0 )) exit=$rc"
DEPS_AFTER=$(manifest); echo "deps_oleans_sha256_after=$DEPS_AFTER"
ls -la "$OUT" 2>/dev/null
tail -5 "$OUT/build.log" 2>/dev/null
exit $rc
