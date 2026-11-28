import Research.R2ContentCompletion.Controls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness
open R2CompletionControls R2SequenceControls R2CompactControls R2ConcreteSuppliers

namespace R2LandedControls

def source : String := "? ?\n    - a\n    - b\n  : c\n: d\n"
def afterInner : ScannerState := afterFirstColon source
def afterOuter : ScannerState := (nthColon source 1).getD (ScannerState.mk' source)

-- Initialization and isSome guards exclude fallback default states.
example : (nthQuestion source 0).isSome = true := by decide +kernel
example : (nthQuestion source 1).isSome = true := by decide +kernel
example : (nthDash source 0).isSome = true := by decide +kernel
example : (nthDash source 1).isSome = true := by decide +kernel
example : (nthColon source 0).isSome = true := by decide +kernel
example : (nthColon source 1).isSome = true := by decide +kernel
lemma rootMarks : markedCols (questionState source 0) = [0] := by decide +kernel
lemma innerMarks : markedCols (questionState source 1) = [0,2] := by decide +kernel
lemma landedMarks : markedCols (dashState source 0) = [0,2] := by decide +kernel
lemma siblingMarks : markedCols (dashState source 1) = [0,2] := by decide +kernel
lemma innerConsumedMarks : markedCols afterInner = [0] := by decide +kernel
lemma outerConsumedMarks : markedCols afterOuter = [] := by decide +kernel
example : (dashState source 0).offset = 9 ∧ (dashState source 0).col = 5 := by decide +kernel
example : (questionState source 1).offset = 3 ∧ (questionState source 1).col = 3 := by decide +kernel
example : (nthDash "" 0).isNone := by decide +kernel
example : markedCols (ScannerState.mk' source) = [] := by decide +kernel

#guard (L4YAML.TokenParser.parseYaml source).isOk
#guard (L4YAML.TokenParser.parseYaml "?\n  - a\n  - b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml "?\n- a\n: b\n").isOk

end R2LandedControls
