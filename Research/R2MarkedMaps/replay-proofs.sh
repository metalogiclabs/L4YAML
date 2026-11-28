#!/usr/bin/env bash
set -euo pipefail
: "${R2_BASE_LIB:?Qualified #392 accepted Lean library required}"
: "${R2_JOINT_LIB:?Checked joint and parent research modules required}"
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_out="$task_root/verification/marked-maps-replay"
task_logs="$task_root/Research/R2MarkedMaps/logs"
mkdir -p "$task_out/Research/R2MarkedMaps" "$task_logs"
for task_parent in R2JointFrames R2ConsumptionClosure R2InvariantPayload R2CompactSlot R2SequenceContext R2ContentCompletion R2ContinuationContract R2UnmarkedOwner R2ValueOwnership; do
  test -d "$R2_JOINT_LIB/Research/$task_parent"
  if [ ! -e "$task_out/Research/$task_parent" ]; then
    ln -s "$R2_JOINT_LIB/Research/$task_parent" "$task_out/Research/$task_parent"
  fi
done
export LEAN_PATH="$task_out:$R2_BASE_LIB"
for task_module in Adversarial Writers Stages Reachable NativeBoundary Producers Concrete DependencyAudit; do
  task_name=${task_module,,}
  task_exit=0
  "$R2_LEAN_BIN" -j 1 -o "$task_out/Research/R2MarkedMaps/$task_module.olean" "Research/R2MarkedMaps/$task_module.lean" > "$task_logs/$task_name.log" 2>&1 || task_exit=$?
  printf '%s\n' "$task_exit" > "$task_logs/$task_name.exit"
  if [ "$task_exit" -ne 0 ]; then
    printf 'FAILED Research/R2MarkedMaps/%s\n' "$task_module"
    exit "$task_exit"
  fi
  printf 'CHECKED Research/R2MarkedMaps/%s\n' "$task_module"
done
