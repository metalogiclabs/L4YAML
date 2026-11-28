#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2CloseValueFamily/reconstruct.sh
task_replay="$task_root/verification/joint-reconstruction"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
task_sources="$task_replay/sources"
mkdir -p "$(dirname "$task_source")" "$task_sources"
cp verification/close-reconstruction/sources/funded.lean "$task_source"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2JointFrames/total-block.patch
cp "$task_source" "$task_sources/total-block.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean Research/R2UnmarkedOwner/ProducerAudit.inc.lean Research/R2UnmarkedOwner/CompositionAudit.inc.lean Research/R2CloseValueFamily/ProductionAudit.inc.lean Research/R2JointFrames/TotalAudit.inc.lean > "$task_sources/audited.lean"
awk '/^lemma scanFlowSequenceStart_tokens/{exit} {print}' "$task_source" > "$task_sources/prefix.lean"
printf '\nend L4YAML.Proofs.StreamAccum\nend Blanket\n' >> "$task_sources/prefix.lean"
cat Research/R2CloseValueFamily/PrefixAudit.inc.lean Research/R2JointFrames/TotalPrefixAudit.inc.lean >> "$task_sources/prefix.lean"
cp verification/close-reconstruction/sources/funded.lean "$task_source"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2JointFrames/remove-block-field.patch
cp "$task_source" "$task_sources/removed.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean Research/R2UnmarkedOwner/ProducerAudit.inc.lean Research/R2UnmarkedOwner/CompositionAudit.inc.lean Research/R2CloseValueFamily/ProductionAudit.inc.lean Research/R2JointFrames/RemovedAudit.inc.lean > "$task_sources/removed-audited.lean"
awk '/^lemma scanFlowSequenceStart_tokens/{exit} {print}' "$task_source" > "$task_sources/removed-prefix.lean"
printf '\nend L4YAML.Proofs.StreamAccum\nend Blanket\n' >> "$task_sources/removed-prefix.lean"
cat Research/R2CloseValueFamily/PrefixAudit.inc.lean Research/R2JointFrames/RemovedPrefixAudit.inc.lean >> "$task_sources/removed-prefix.lean"
sha256sum -c Research/R2JointFrames/SOURCES.sha256
if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Original matching accepted library required}"
  : "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
  export LEAN_PATH="$R2_BASE_LIB"
  for task_variant in audited removed-audited; do
    cp "$task_sources/$task_variant.lean" "$task_source"
    if "$R2_LEAN_BIN" -j 1 "$task_source" > "$task_replay/$task_variant.log" 2>&1; then task_status=0; else task_status=$?; fi
    printf '%s exit=%s\n' "$task_variant" "$task_status"
    test "$task_status" -eq 1
  done
  for task_variant in prefix removed-prefix; do
    cp "$task_sources/$task_variant.lean" "$task_source"
    "$R2_LEAN_BIN" -j 1 -o "$task_replay/$task_variant.olean" "$task_source" > "$task_replay/$task_variant.log" 2>&1
    printf '%s exit=0 (isolated accepted object)\n' "$task_variant"
  done
fi
