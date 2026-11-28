#!/usr/bin/env bash
set -euo pipefail
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2UnmarkedOwner/reconstruct.sh
task_replay="$task_root/verification/close-reconstruction"
task_source="$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
task_sources="$task_replay/sources"
mkdir -p "$(dirname "$task_source")" "$task_sources"
for task_variant in initial funded-draft funded; do
  cp verification/unmarked-reconstruction/sources/integrated.lean "$task_source"
  patch --fuzz=0 -s -p1 -d "$task_replay" < "Research/R2CloseValueFamily/$task_variant.patch"
  cp "$task_source" "$task_sources/$task_variant.lean"
done
cat "$task_source" Research/R2CloseValueFamily/ProductionAudit.inc.lean > "$task_sources/funded-audited.lean"
cat "$task_source" Research/R2ContinuationContract/ProductionAudit.inc.lean Research/R2UnmarkedOwner/ProducerAudit.inc.lean Research/R2UnmarkedOwner/CompositionAudit.inc.lean Research/R2CloseValueFamily/ProductionAudit.inc.lean > "$task_sources/final-audited.lean"
patch --fuzz=0 -s -p1 -d "$task_replay" < Research/R2CloseValueFamily/erased-reader.patch
cp "$task_source" "$task_sources/erased-reader.lean"
awk '/^lemma scanFlowSequenceStart_tokens/{exit} {print}' "$task_sources/funded.lean" > "$task_sources/flow-prefix.lean"
printf '\nend L4YAML.Proofs.StreamAccum\nend Blanket\n' >> "$task_sources/flow-prefix.lean"
cat Research/R2CloseValueFamily/PrefixAudit.inc.lean >> "$task_sources/flow-prefix.lean"
sha256sum -c Research/R2CloseValueFamily/SOURCES.sha256

if [ "${1:-}" = --compile ]; then
  : "${R2_BASE_LIB:?Original matching accepted library required}"
  : "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
  export LEAN_PATH="$R2_BASE_LIB"
  for task_variant in final-audited erased-reader; do
    cp "$task_sources/$task_variant.lean" "$task_source"
    if "$R2_LEAN_BIN" -j 1 "$task_source" > "$task_replay/$task_variant.log" 2>&1; then task_status=0; else task_status=$?; fi
    printf '%s exit=%s\n' "$task_variant" "$task_status"
    test "$task_status" -eq 1
  done
  cp "$task_sources/flow-prefix.lean" "$task_source"
  "$R2_LEAN_BIN" -j 1 -o "$task_replay/FlowPrefix.olean" "$task_source" > "$task_replay/flow-prefix.log" 2>&1
  printf 'flow-prefix exit=0 (isolated accepted object)\n'
fi
