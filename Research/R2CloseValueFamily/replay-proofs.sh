#!/usr/bin/env bash
set -euo pipefail
: "${R2_BASE_LIB:?Qualified #392 accepted Lean library required}"
: "${R2_RESEARCH_LIB:?24 checked parent research modules required}"
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_out="$task_root/verification/close-proofs"
task_logs="$task_root/Research/R2CloseValueFamily/logs/standalone"
mkdir -p "$task_out/Research/R2CloseValueFamily" "$task_out/Research/R2ColonComposition" "$task_out/Research/R2ColonSupplier" "$task_logs"
for task_parent in R2ConsumptionClosure R2InvariantPayload R2CompactSlot R2SequenceContext R2ContentCompletion R2ContinuationContract R2UnmarkedOwner R2ValueOwnership; do
  test -d "$R2_RESEARCH_LIB/Research/$task_parent"
  if [ ! -e "$task_out/Research/$task_parent" ]; then
    ln -s "$R2_RESEARCH_LIB/Research/$task_parent" "$task_out/Research/$task_parent"
  fi
done
export LEAN_PATH="$task_out:$R2_BASE_LIB"
for task_module in \
  Research/R2ColonComposition/ColonValues \
  Research/R2ColonSupplier/Controls \
  Research/R2ColonSupplier/ConsumedSibling \
  Research/R2ColonSupplier/LiveOwner \
  Research/R2CloseValueFamily/Controls \
  Research/R2CloseValueFamily/PairRoute \
  Research/R2CloseValueFamily/Concrete \
  Research/R2CloseValueFamily/DependencyAudit; do
  task_name=${task_module//\//-}
  "$R2_LEAN_BIN" -j 1 -o "$task_out/$task_module.olean" "$task_module.lean" > "$task_logs/$task_name.log" 2>&1
  printf 'CHECKED %s\n' "$task_module"
done
