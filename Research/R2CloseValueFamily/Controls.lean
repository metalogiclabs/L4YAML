import Research.R2UnmarkedOwner.Controls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness
open R2ConcreteSuppliers R2CompactControls

namespace R2CloseControls

def fuelRun (input : String) : Nat → Option ScannerState
  | 0 => some ((ScannerState.mk' input).emit .streamStart)
  | n + 1 => (fuelRun input n).bind fun s =>
      match scanNextToken s with | .ok (some s') => some s' | _ => none

example : (fuelRun "" 0).isSome = true := by decide +kernel
example : (fuelRun "? a\n: b\n" 1).isSome = true := by decide +kernel
example : (fuelRun "? ? a\n  : b\n: c\n" 2).isSome = true := by decide +kernel
example : markedCols (afterFirstColon "? ? a\n  : b\n  : c\n: d\n") = [0] := by decide +kernel
#guard (L4YAML.TokenParser.parseYaml "? ? [a]\n  : b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? {a: b}\n  : c\n: d\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? &p a\n  : b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? !foo &p a\n  : b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? |\n    a\n  : b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? - a\n    - b\n  : c\n: d\n").isOk

end R2CloseControls
