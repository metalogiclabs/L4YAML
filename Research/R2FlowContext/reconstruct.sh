#!/usr/bin/env bash
set -euo pipefail
: "${R2_LEAN_BIN:?Pinned Lean 4.36.0 binary required}"
task_root=$(git rev-parse --show-toplevel)
cd "$task_root"
task_replay="$task_root/verification/flow-context-replay"
task_parent="$task_replay/parent.lean"
task_audited="$task_replay/audited"
task_erased="$task_replay/erased"
mkdir -p "$task_audited/L4YAML/Proofs/Production" "$task_erased/L4YAML/Proofs/Production"
cp L4YAML/Proofs/Production/StreamAccum.lean "$task_parent"
printf '%s\n' "f1eece1acca9f124666aa8fcc8fe5b591c316df35b292b32ed28af491a25772a  $task_parent" | sha256sum -c -
base64 --decode Research/R2SequenceRetirement/Draft.patch.xz.b64 | xz --decompress > "$task_replay/parent.patch"
patch --fuzz=0 -s "$task_parent" < "$task_replay/parent.patch"
printf '%s\n' "d3589230b768b92f8fac3df21535b7aa199a25f0f5228a4b67c65cf05ebcc193  $task_parent" | sha256sum -c -
"$R2_LEAN_BIN" --run Research/R2FlowContext/Prepare.lean "$task_parent" \
  "$task_audited/L4YAML/Proofs/Production/StreamAccum.lean" --fund-six
"$R2_LEAN_BIN" --run Research/R2FlowContext/Erase.lean \
  "$task_audited/L4YAML/Proofs/Production/StreamAccum.lean" \
  "$task_erased/L4YAML/Proofs/Production/StreamAccum.lean"
printf '%s\n' "416aa519de2d988a37364a05bf6768b03420d49b9781b352130a0987d57d1c6b  $task_audited/L4YAML/Proofs/Production/StreamAccum.lean" \
  "8fe4c5fc76c96e93a2b06ae7cf4c34b55518f8a697d253f8c209ad547b46159c  $task_erased/L4YAML/Proofs/Production/StreamAccum.lean" | sha256sum -c -
if [ "${1:-}" = --compile ]; then
  : "${R2_RESEARCH_LIB:?Matching checked scanner ownership imports required}"
  : "${R2_BASE_LIB:?Matching accepted production imports required}"
  export LEAN_PATH="$R2_RESEARCH_LIB:$R2_BASE_LIB"
  for task_variant in audited erased; do
    task_dir="$task_audited"
    if [ "$task_variant" = erased ]; then task_dir="$task_erased"; fi
    task_exit=0
    (cd "$task_dir"; "$R2_LEAN_BIN" -j1 L4YAML/Proofs/Production/StreamAccum.lean) \
      > "Research/R2FlowContext/logs/$task_variant.log" 2>&1 || task_exit=$?
    printf '%s\n' "$task_exit" > "Research/R2FlowContext/logs/$task_variant.exit"
    test "$task_exit" -eq 1
    xz --compress --stdout "Research/R2FlowContext/logs/$task_variant.log" | base64 -w 76 \
      > "Research/R2FlowContext/logs/$task_variant.log.xz.b64"
  done
  "$R2_LEAN_BIN" --run Research/R2FlowContext/Verify.lean
fi
