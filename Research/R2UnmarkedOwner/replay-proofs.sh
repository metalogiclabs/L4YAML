#!/usr/bin/env bash
set -euo pipefail
: "${R2_BASE_LIB:?Matching accepted Lean library required}"
: "${R2_RESEARCH_LIB:?18 checked parent research modules are required}"
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_out="$task_root/verification/unmarked-proofs"
task_logs="$task_root/Research/R2UnmarkedOwner/logs/standalone"
mkdir -p "$task_out/Research/R2UnmarkedOwner" "$task_out/Research/R2ValueOwnership" "$task_logs"
for task_parent in R2ConsumptionClosure R2InvariantPayload R2CompactSlot R2SequenceContext R2ContentCompletion R2ContinuationContract; do
  test -d "$R2_RESEARCH_LIB/Research/$task_parent"
  if [ ! -e "$task_out/Research/$task_parent" ]; then
    ln -s "$R2_RESEARCH_LIB/Research/$task_parent" "$task_out/Research/$task_parent"
  fi
done
export LEAN_PATH="$task_out:$R2_BASE_LIB"
for task_module in \
  Research/R2UnmarkedOwner/Controls \
  Research/R2UnmarkedOwner/AncestorValue \
  Research/R2UnmarkedOwner/Concrete \
  Research/R2UnmarkedOwner/Payloads \
  Research/R2ValueOwnership/Ownership \
  Research/R2UnmarkedOwner/DependencyAudit; do
  task_name=${task_module//\//-}
  "$R2_LEAN_BIN" -o "$task_out/$task_module.olean" "$task_module.lean" > "$task_logs/$task_name.log" 2>&1
  printf 'CHECKED %s\n' "$task_module"
done
