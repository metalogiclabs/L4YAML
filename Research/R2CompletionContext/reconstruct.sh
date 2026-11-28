#!/usr/bin/env bash
set -euo pipefail
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
bash Research/R2MandatoryContext/reconstruct.sh
task_base="$task_root/verification/mandatory-migration-replay/L4YAML/Proofs/Production/StreamAccum.lean"
printf '%s\n' "f4898e17ca902b360e8801650d3588e8c73511dd04003549f7ff0ff9921ca3d5  $task_base" | sha256sum -c -
task_replay="$task_root/verification/completion-context-replay"
task_erased="$task_root/verification/completion-context-erased"
mkdir -p "$task_replay/L4YAML/Proofs/Production" "$task_erased/L4YAML/Proofs/Production"
"$R2_LEAN_BIN" --run Research/R2CompletionContext/Prepare.lean "$task_base" \
  "$task_replay/L4YAML/Proofs/Production/StreamAccum.lean"
"$R2_LEAN_BIN" --run Research/R2CompletionContext/Erase.lean \
  "$task_replay/L4YAML/Proofs/Production/StreamAccum.lean" \
  "$task_erased/L4YAML/Proofs/Production/StreamAccum.lean"
printf '%s\n' "8e2bd5004d77c7acb59aedfdcab6e54059b2d39f6df4b55d7c36d7fd9581984b  $task_replay/L4YAML/Proofs/Production/StreamAccum.lean" \
  "1193ca6b16aba89c2e848a1ec30076a4aba50e6a9921753bba282d94d5fed710  $task_erased/L4YAML/Proofs/Production/StreamAccum.lean" | sha256sum -c -
if [ "${1:-}" = --compile ]; then
  : "${R2_MAP_LIB:?Checked scanner ownership modules required}"
  : "${R2_DIAGNOSTIC_LIB:?Original matching accepted 9f1f7bc6 production imports required}"
  export LEAN_PATH="$R2_MAP_LIB:$R2_DIAGNOSTIC_LIB"
  for task_variant in audited erased; do
    task_dir="$task_replay"
    if [ "$task_variant" = erased ]; then task_dir="$task_erased"; fi
    task_exit=0
    (cd "$task_dir"; "$R2_LEAN_BIN" -j1 L4YAML/Proofs/Production/StreamAccum.lean) \
      > "Research/R2CompletionContext/logs/$task_variant.log" 2>&1 || task_exit=$?
    printf '%s\n' "$task_exit" > "Research/R2CompletionContext/logs/$task_variant.exit"
    test "$task_exit" -eq 1
    xz --compress --stdout "Research/R2CompletionContext/logs/$task_variant.log" | base64 -w 76 \
      > "Research/R2CompletionContext/logs/$task_variant.log.xz.b64"
  done
  "$R2_LEAN_BIN" --run Research/R2CompletionContext/Verify.lean
fi
