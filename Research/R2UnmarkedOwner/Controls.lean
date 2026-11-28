import Research.R2ContinuationContract.Controls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness
open R2ConcreteSuppliers R2CompactControls R2SequenceControls

namespace R2UnmarkedControls

def source : String := "? ? a\n  : - b\n  : c\n: d\n"
def consumed : ScannerState := afterFirstColon source
example : (firstColon source).isSome = true := by decide +kernel
example : (nthDash source 0).isSome = true := by decide +kernel
example : markedCols consumed = [0] := by decide +kernel
example : 2 ∉ markedCols consumed := by decide +kernel
example : markedCols (dashState source 0) = [0] := by decide +kernel
example : (nthColon source 1).isSome = true := by decide +kernel
#guard (L4YAML.TokenParser.parseYaml source).isOk
#guard (L4YAML.TokenParser.parseYaml "? ? - a\n    - b\n  : c\n: d\n").isOk

end R2UnmarkedControls
