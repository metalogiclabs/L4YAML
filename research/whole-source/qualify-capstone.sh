#!/usr/bin/env bash
# Reusable, source-bound qualification entrypoint. No semantic promotion is
# inferred from the ledger or process exit alone: inspect theorem types/axioms.
set -euo pipefail
cd -- "$(git rev-parse --show-toplevel)"
out=${1:-capstone-evidence}
test ! -e "$out/status.tsv"
mkdir -p "$out"
baseline=64795a8db28ccfdae85082c93b6453001ae9d3e4
bash research/whole-source/source-identity.sh record "$baseline" "$out"
lean --version | tee "$out/lean-version.txt"
grep -F 'version 4.35.0' "$out/lean-version.txt"
trap 'bash research/whole-source/source-identity.sh verify "$baseline" "$out"' EXIT

lake build L4YAML.Proofs.Serialization.TraceOf.Document L4YAML.Parser.Composition \
  L4YAML.Proofs.Production.Acceptance.Properties L4YAML.Proofs.Production.Acceptance.Plain \
  L4YAML.Proofs.Scanner.ScannerCorrectness L4YAML.Proofs.Output.EmitterScannability.ScanSteps \
  L4YAML.Proofs.Scanner.ScanStrictCoupling L4YAML.Proofs.Scanner.IndentStackBase \
  L4YAML.Proofs.Parser.StreamCompleteness \
  L4YAML.Proofs.Scanner.ScannerFlowStackPreservation L4YAML.Proofs.Coupling.StructureCoupling \
  L4YAML.Proofs.Output.EmitterScannability.FilteredTracking > "$out/baseline.log" 2>&1

export LEAN_PATH="$PWD/research/structural-boundaries:$PWD/research/accepted-source:$PWD/research/whole-source:$(lake env printenv LEAN_PATH)"
compile() {
  local dir=$1 name=$2 status
  if lean --root="$dir" -o "$dir/$name.olean" "$dir/$name.lean" > "$out/$name.log" 2>&1; then status=0; else status=$?; fi
  printf '%s\t%s\n' "$name" "$status" | tee -a "$out/status.tsv"
  cat "$out/$name.log"
  test "$status" = 0
  if grep -E 'sorryAx|declaration uses .sorry.|Unknown constant|unknown module prefix|unexpected token' "$out/$name.log"; then return 1; fi
}

compile research/structural-boundaries TraceExplicitRepairAudit
compile research/accepted-source QuotedPublic
# Unchanged source-positive and source-negative controls are part of the run.
compile research/accepted-source QuotedPublicControls
for name in DirectiveControls DirectiveTrace DirectiveConsumer DirectiveDiscipline DirectiveDisciplineConsumer DirectiveSufficiency DirectiveBridge DirectiveBridgeConsumer DirectiveTransfer DirectiveDispatch DirectiveComments DirectiveBoundary DirectiveStep DirectiveEntry DirectiveEOF DirectiveParse DirectiveResult CapstoneObstructions CapstoneCommentBoundary CapstoneQualification; do
  compile research/whole-source "$name"
done

python3 research/whole-source/coverage-audit.py > "$out/coverage-census.log"
compile research/whole-source ExactCharacters
test "$(grep -c EXACT_CHARACTERS_AXIOMS "$out/ExactCharacters.log")" = 6
compile research/whole-source ExactLexical
compile research/whole-source ExactLexicalBridge
test "$(grep -c EXACT_LEXICAL_AXIOMS "$out/ExactLexicalBridge.log")" = 8
compile research/whole-source ExactQuoted
compile research/whole-source ExactQuotedChecks
test "$(grep -c EXACT_QUOTED_AXIOMS "$out/ExactQuotedChecks.log")" = 10
compile research/whole-source AcceptanceScope
test "$(grep -c ACCEPTANCE_SCOPE_AXIOMS "$out/AcceptanceScope.log")" = 2
compile research/whole-source SourceBridge
compile research/whole-source FlowProducerCase
test "$(grep -c FLOW_PRODUCER_CASE_AXIOMS "$out/FlowProducerCase.log")" = 1
compile research/whole-source FlowCloseLanding
test "$(grep -c FLOW_CLOSE_LANDING_AXIOMS "$out/FlowCloseLanding.log")" = 2
compile research/whole-source CoverageInventory
compile research/whole-source DirectiveRecords
compile research/whole-source DirectiveRecordBridge
compile research/whole-source TagDocument
compile research/whole-source QuotedContinuation
compile research/whole-source TagQuotedParse
test "$(grep -c TAG_QUOTED_PARSE_AXIOMS "$out/TagQuotedParse.log")" = 2
test "$(grep -c QUOTED_CONTINUATION_AXIOMS "$out/QuotedContinuation.log")" = 2
test "$(grep -c TAG_DOCUMENT_AXIOMS "$out/TagDocument.log")" = 4
test "$(grep -c DIRECTIVE_RECORD_BRIDGE_AXIOMS "$out/DirectiveRecordBridge.log")" = 5
test "$(grep -c DIRECTIVE_RECORD_AXIOMS "$out/DirectiveRecords.log")" = 15
test "$(grep -c 'SOURCE_BRIDGE_AXIOMS' "$out/SourceBridge.log")" = 4

# A required RED is an exact false proposition, never an import/syntax failure.
if lean --root=research/whole-source research/whole-source/DirectiveRed.lean > "$out/DirectiveRed.log" 2>&1; then status=0; else status=$?; fi
printf 'DirectiveRed-expected-failure\t%s\n' "$status" | tee -a "$out/status.tsv"
test "$status" = 1
test "$(grep -c ': error:' "$out/DirectiveRed.log")" = 1
test "$(grep -Eci ': error:.*native_decide.*evaluated.*proposition' "$out/DirectiveRed.log")" = 1
test "$(grep -c 'QUALIFIED_AXIOMS' "$out/CapstoneQualification.log")" = 7
bash research/whole-source/source-identity.sh verify "$baseline" "$out"
printf '%s\n' 'Qualification passed at the printed theorem boundaries; Group 7.7 remains open.'
