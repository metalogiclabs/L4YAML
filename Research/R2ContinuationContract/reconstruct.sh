#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_replay="$task_root/verification/diagnostic-replay"
task_sources="$task_root/verification/sources"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
mkdir -p "$(dirname "$task_source")" "$task_sources"
git show 9f1f7bc6:L4YAML/Proofs/Production/StreamAccum.lean > "$task_source"
for task_patch in \
  Research/R2EntryPreservation/retention-original.patch \
  Research/R2EntryPreservation/retention-strict-delta.patch \
  Research/R2SurvivorDomain/retention-refinements.patch \
  Research/R2ConsumptionClosure/producer-domain.patch \
  Research/R2InvariantPayload/invariant-payload.patch \
  Research/R2CompactSlot/compact-slot.patch \
  Research/R2SequenceContext/sequence-context.patch; do
  patch -s -p1 -d "$task_replay" < "$task_patch"
done
cp "$task_source" "$task_sources/sequence-parent.lean"
patch -s -p1 -d "$task_replay" < Research/R2ContentCompletion/content-completion.patch
cp "$task_source" "$task_sources/completion-draft.lean"
patch -s -p1 -d "$task_replay" < Research/R2ContinuationContract/marked-pair.patch
cp "$task_source" "$task_sources/marked-pair.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean \
  > "$task_sources/audited-positive.lean"
patch -s -p1 -d "$task_replay" < Research/R2ContinuationContract/erased-family.patch
cp "$task_source" "$task_sources/erased-family.lean"
sha256sum -c Research/R2ContinuationContract/SOURCES.sha256

if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Set R2_BASE_LIB to the matching accepted library}"
  : "${R2_LEAN_BIN:?Set R2_LEAN_BIN to the pinned Lean binary}"
  export LEAN_PATH="$R2_BASE_LIB"
  for task_variant in completion-draft marked-pair audited-positive erased-family; do
    cp "$task_sources/$task_variant.lean" "$task_source"
    if (cd "$task_replay" && "$R2_LEAN_BIN" L4YAML/Proofs/Production/StreamAccum.lean) \
        > "$task_root/verification/$task_variant.log" 2>&1; then
      task_status=0
    else
      task_status=$?
    fi
    printf '%s exit=%s\n' "$task_variant" "$task_status"
    test "$task_status" -eq 1
  done
fi
