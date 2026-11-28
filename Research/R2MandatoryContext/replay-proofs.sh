#!/usr/bin/env bash
set -euo pipefail
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
: "${R2_BASE_LIB:?Matching accepted qualified production library required}"
: "${R2_PARENT_LIB:?Matching checked continuation research library required}"
: "${R2_MAP_LIB:?Checked ee5739cc scanner ownership and joint snapshots required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_out="$task_root/verification/mandatory-proof-replay"
task_logs="$task_root/Research/R2MandatoryContext/logs"
mkdir -p "$task_out/Research/R2MandatoryContext" "$task_logs"
export LEAN_PATH="$task_out:$R2_MAP_LIB:$R2_PARENT_LIB:$R2_BASE_LIB"
for task_module in Controls Births Completion Values Witness Audit; do
  task_name=${task_module,,}
  task_exit=0
  "$R2_LEAN_BIN" -j1 -o "$task_out/Research/R2MandatoryContext/$task_module.olean" \
    "Research/R2MandatoryContext/$task_module.lean" > "$task_logs/$task_name.log" 2>&1 || task_exit=$?
  printf '%s\n' "$task_exit" > "$task_logs/$task_name.exit"
  if [ "$task_exit" -ne 0 ]; then
    rm -f "$task_out/Research/R2MandatoryContext/$task_module.olean"
    printf 'FAILED %s\n' "$task_module"
    exit "$task_exit"
  fi
  printf 'CHECKED %s\n' "$task_module"
done
task_exit=0
"$R2_LEAN_BIN" -j1 Research/R2MandatoryContext/ErasedReader.lean > "$task_logs/erased-reader.log" 2>&1 || task_exit=$?
printf '%s\n' "$task_exit" > "$task_logs/erased-reader.exit"
test "$task_exit" -eq 1
printf 'EXPECTED REJECTION erased-reader\n'
for task_log in "$task_logs"/*.log; do
  xz --compress --stdout "$task_log" | base64 -w 76 > "$task_log.xz.b64"
done
