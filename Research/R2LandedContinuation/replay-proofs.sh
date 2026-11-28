#!/usr/bin/env bash
set -euo pipefail
: "${R2_BASE_LIB:?Set R2_BASE_LIB to the accepted library build/lib/lean}"
: "${R2_LEAN_BIN:?Set R2_LEAN_BIN to the pinned Lean 4.36.0 binary}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_label=${R2_REPLAY_LABEL:-cold}
task_output="$task_root/verification/landed-$task_label"
task_logs="$task_root/verification/landed-$task_label-logs"
mkdir -p "$task_output/Research" "$task_logs"
export LEAN_PATH="$task_output:$R2_BASE_LIB"
task_modules=(
  Research/R2ContinuationContract/EntryRoutes
  Research/R2ConsumptionClosure/EntryValues
  Research/R2ConsumptionClosure/ConcreteSuppliers
  Research/R2InvariantPayload/NodeValues
  Research/R2InvariantPayload/SourceControls
  Research/R2InvariantPayload/ConcretePayloads
  Research/R2CompactSlot/SlotValues
  Research/R2CompactSlot/Controls
  Research/R2SequenceContext/SequenceValues
  Research/R2SequenceContext/Controls
  Research/R2SequenceContext/ConcreteContexts
  Research/R2ContentCompletion/Controls
  Research/R2ContentCompletion/CompletedValues
  Research/R2ContentCompletion/ConcreteCompletion
  Research/R2ContentCompletion/DependencyAudit
  Research/R2ContinuationContract/Controls
  Research/R2ContinuationContract/TwoAncestors
  Research/R2ContinuationContract/DependencyAudit
  Research/R2LandedContinuation/LandedValues
  Research/R2LandedContinuation/Controls
  Research/R2LandedContinuation/TwoAncestors
  Research/R2LandedContinuation/DependencyAudit
)
for task_module in "${task_modules[@]}"; do
  mkdir -p "$task_output/$(dirname "$task_module")"
  "$R2_LEAN_BIN" -o "$task_output/$task_module.olean" "$task_module.lean" \
    > "$task_logs/${task_module//\//-}.log" 2>&1
  printf 'CHECKED %s\n' "$task_module"
done
if [ "${R2_CHECK_QUALIFIED_OWNER:-0}" = 1 ]; then
  "$R2_LEAN_BIN" Research/R2LandedContinuation/QualifiedOwnerAudit.lean \
    > "$task_logs/QualifiedOwnerAudit.log" 2>&1
fi
if "$R2_LEAN_BIN" Research/R2LandedContinuation/ErasedReader.lean \
    > "$task_logs/erased-reader.log" 2>&1; then task_status=0; else task_status=$?; fi
printf '%s\n' "$task_status" > "$task_logs/erased-reader.exit"
test "$task_status" -eq 1
cat "$task_logs/Research-R2LandedContinuation-DependencyAudit.log"
