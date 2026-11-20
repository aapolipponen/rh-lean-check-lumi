#!/bin/bash
# LUMI-C: coordinator on the first node, one worker per node.
#   sbatch -N 8 -t 02:00:00 [-p standard] lumi-run.sbatch [coord args, e.g. --mode build]
# Billing: standard = 128 cores x nodes x wall.  Resume by submitting again.
#SBATCH --account=project_462001825
#SBATCH --partition=standard
#SBATCH --job-name=rh-check
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=128
#SBATCH --output=/flash/project_462001825/rieman/logs/%x-%j.out
set -uo pipefail
B=${RH_BASE:-/flash/project_462001825/rieman}
R=$B/rhcheck
export ELAN_HOME=$B/elan
module load cray-python 2>/dev/null || true
SLOTS=${RH_SLOTS:-$SLURM_CPUS_PER_TASK}
mkdir -p "$B/state" "$B/logs"
rm -f "$B/state/coord.addr"
[ -f "$B/conf.json" ] || "$R/mkconf.sh" "$B" > "$B/conf.json"
echo "[job] nodes=$SLURM_JOB_NUM_NODES slots/node=$SLOTS args=$*"
python3 "$R/dbuild.py" coord --conf "$B/conf.json" "$@" &
COORD=$!
srun --nodes="$SLURM_JOB_NUM_NODES" --ntasks="$SLURM_JOB_NUM_NODES" --ntasks-per-node=1 \
     --cpus-per-task="$SLURM_CPUS_PER_TASK" --cpu-bind=none --kill-on-bad-exit=0 \
     python3 "$R/dbuild.py" work --state "$B/state" --slots "$SLOTS" \
     --sandbox "${RH_SANDBOX:-auto}" --image "$B/sandbox.sif" --stage "${RH_STAGE-/dev/shm}" --tmp /tmp
wait $COORD
rc=$?
echo "[job] coordinator exit $rc"
exit $rc
