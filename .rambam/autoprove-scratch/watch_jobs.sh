#!/bin/bash
# Watch Aristotle jobs until all reach a terminal state; download each result.
# Usage: watch_jobs.sh <id> [<id> ...]
set -a; source /Users/elanroth/pure/Rambam/.env; set +a
cd /Users/elanroth/pure/Lean/compfiles || exit 1
RAM=/Users/elanroth/pure/Rambam/.venv/bin/rambam
PENDING=("$@")
for i in $(seq 1 30); do
  STILL=()
  for id in "${PENDING[@]}"; do
    st=$($RAM -p . poll "$id" 2>&1 | grep -o 'Status: .*' | sed 's/Status: //' | sed 's/\x1b\[[0-9;]*m//g')
    case "$st" in
      *pending*|*in_progress*) STILL+=("$id");;
      *) echo "$(date +%H:%M) $id TERMINAL: $st"
         $RAM -p . poll "$id" --wait -o ".rambam/autoprove-scratch/job_${id:0:8}.lean" 2>&1 | tail -3;;
    esac
  done
  PENDING=("${STILL[@]}")
  [ ${#PENDING[@]} -eq 0 ] && break
  echo "$(date +%H:%M) still pending: ${PENDING[*]}"
  sleep 600
done
echo "watcher done"
