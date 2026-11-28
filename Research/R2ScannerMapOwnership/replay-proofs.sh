#!/usr/bin/env bash
set -euo pipefail
: "${R2_BASE_LIB:?Qualified #392 library is required}"
: "${R2_RESEARCH_LIB:?Matching checked parent research modules are required}"
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary is required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_out="$task_root/verification/map-proof-replay"
task_logs="$task_root/verification/map-proof-replay-logs"
mkdir -p "$task_out/Research/R2ScannerMapOwnership" "$task_out/Research/R2JointFrames" "$task_logs"
for task_parent in "$R2_RESEARCH_LIB"/Research/*; do
  if [ -d "$task_parent" ] && [ ! -e "$task_out/Research/${task_parent##*/}" ]; then
    ln -s "$(readlink -f "$task_parent")" "$task_out/Research/${task_parent##*/}"
  fi
done
export LEAN_PATH="$task_out:$R2_BASE_LIB"
for task_module in Controls Scanner Step Reachable Countermodel; do
  "$R2_LEAN_BIN" -j1 -o "$task_out/Research/R2ScannerMapOwnership/$task_module.olean" \
    "Research/R2ScannerMapOwnership/$task_module.lean" > "$task_logs/$task_module.log" 2>&1
  printf 'CHECKED own/%s\n' "$task_module"
done
for task_module in Controls Joint State Slots; do
  "$R2_LEAN_BIN" -j1 -o "$task_out/Research/R2JointFrames/$task_module.olean" \
    "Research/R2ScannerMapOwnership/lineage/joint/$task_module.lean" > "$task_logs/joint-$task_module.log" 2>&1
  printf 'CHECKED snapshot/%s\n' "$task_module"
done
for task_module in Bridge Audit Verify; do
  "$R2_LEAN_BIN" -j1 -o "$task_out/Research/R2ScannerMapOwnership/$task_module.olean" \
    "Research/R2ScannerMapOwnership/$task_module.lean" > "$task_logs/$task_module.log" 2>&1
  printf 'CHECKED own/%s\n' "$task_module"
done
