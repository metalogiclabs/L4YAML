#!/usr/bin/env bash
set -euo pipefail

: "${R2_LEAN_BIN:?Set R2_LEAN_BIN to Lean 4.36.0}"
: "${R2_BASE_LIB:?Set R2_BASE_LIB to the matching accepted production library}"
: "${R2_RESEARCH_LIB:?Set R2_RESEARCH_LIB to the checked ownership research library}"
task_root="$(cd "$(dirname "$0")/../.." && pwd)"
task_out="${R2_REPLAY_OUT:-$(mktemp -d /tmp/r2-sequence-retirement.XXXXXX)}"
mkdir -p "$task_out/lib/Research/R2SequenceRetirement"
for directory in "$R2_RESEARCH_LIB"/Research/*; do
  name="$(basename "$directory")"
  if [[ "$name" != R2SequenceRetirement && ! -e "$task_out/lib/Research/$name" ]]; then
    ln -s "$directory" "$task_out/lib/Research/$name"
  fi
done
export LEAN_PATH="$task_out/lib:$R2_RESEARCH_LIB:$R2_BASE_LIB"
cd "$task_root"
"$R2_LEAN_BIN" --version > "$task_out/toolchain.txt"
for module in MandatoryContext Geometry Audit; do
  "$R2_LEAN_BIN" -j1 \
    -o "$task_out/lib/Research/R2SequenceRetirement/$module.olean" \
    "Research/R2SequenceRetirement/$module.lean" > "$task_out/$module.log" 2>&1
done
cp Research/R2SequenceRetirement/ReaderErasure.lean.reject "$task_out/ReaderErasure.lean"
if "$R2_LEAN_BIN" -j1 "$task_out/ReaderErasure.lean" > "$task_out/ReaderErasure.log" 2>&1; then
  printf '%s\n' 'FAIL: reader erasure unexpectedly accepted' >&2
  exit 1
fi
[[ "$(rg -c 'error:' "$task_out/ReaderErasure.log")" == 1 ]]
rg -q 'Application type mismatch' "$task_out/ReaderErasure.log"
rg -q 'MANDATORY-WRITER' Research/R2SequenceRetirement/ProductionAudit.inc.lean
printf '%s\n' "PASS: three proof/audit modules, one rejected reader erasure. Receipts: $task_out"

if [[ "${1:-}" == --diagnostic ]]; then
  mkdir -p "$task_out/source-root/L4YAML/Proofs/Production"
  target="$task_out/source-root/L4YAML/Proofs/Production/StreamAccum.lean"
  cp L4YAML/Proofs/Production/StreamAccum.lean "$target"
  base64 --decode Research/R2SequenceRetirement/Draft.patch.xz.b64 | xz --decompress > "$task_out/Draft.patch"
  patch --fuzz=0 --silent "$target" < "$task_out/Draft.patch"
  cd "$task_out/source-root"
  if "$R2_LEAN_BIN" -j1 L4YAML/Proofs/Production/StreamAccum.lean > "$task_out/Draft.log" 2>&1; then
    printf '%s\n' 'The previously rejected draft now accepts; run a fresh census before any retirement claim.'
  else
    rg -q 'MANDATORY-WRITER-AUDIT inventory=7 checked=6' "$task_out/Draft.log"
    printf '%s\n' 'EXPECTED: complete draft rejects; six selected writer terms passed their local audit.'
  fi
fi
