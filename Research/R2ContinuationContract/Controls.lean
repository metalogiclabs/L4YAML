import Research.R2ContentCompletion.Controls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness
open R2CompletionControls R2SequenceControls R2CompactControls R2ConcreteSuppliers

namespace R2ContinuationControls

def source : String := "? ? - a\n    - b\n  : c\n: d\n"
def afterInner : ScannerState := afterFirstColon source
def afterOuter : ScannerState := (nthColon source 1).getD (ScannerState.mk' source)

-- Controls precede the new proof. Every scanner projection comes from a real
-- initialized run, and isSome guards exclude the default-state alternative.
example : (nthQuestion source 0).isSome = true := by decide +kernel
example : (nthQuestion source 1).isSome = true := by decide +kernel
example : (nthDash source 0).isSome = true := by decide +kernel
example : (nthDash source 1).isSome = true := by decide +kernel
example : (firstScalar source).isSome = true := by decide +kernel
example : (nthColon source 0).isSome = true := by decide +kernel
example : (nthColon source 1).isSome = true := by decide +kernel
lemma rootMarks : markedCols (questionState source 0) = [0] := by decide +kernel
lemma innerMarks : markedCols (questionState source 1) = [0,2] := by decide +kernel
lemma firstDashMarks : markedCols (dashState source 0) = [0,2] := by decide +kernel
lemma completedMarks : markedCols (scalarState source) = [0,2] := by decide +kernel
lemma siblingMarks : markedCols (dashState source 1) = [0,2] := by decide +kernel
lemma innerConsumedMarks : markedCols afterInner = [0] := by decide +kernel
lemma outerConsumedMarks : markedCols afterOuter = [] := by decide +kernel
example : (scalarState source).offset = 7 ∧ (scalarState source).col = 7 := by decide +kernel
example : (dashState source 1).col = 5 := by decide +kernel
example : afterInner.col = 3 := by decide +kernel
example : afterOuter.col = 1 := by decide +kernel
example : (nthDash "" 0).isNone := by decide +kernel
example : (firstScalar "").isNone := by decide +kernel
example : markedCols (ScannerState.mk' source) = [] := by decide +kernel

#guard (L4YAML.TokenParser.parseYaml source).isOk
#guard (L4YAML.TokenParser.parseYaml "? - a\n  - b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? - &p a\n    - b\n  : c\n: d\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? - |\n      a\n    - b\n  : c\n: d\n").isOk

end R2ContinuationControls
