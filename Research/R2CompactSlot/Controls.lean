import Research.R2InvariantPayload.ConcretePayloads
import L4YAML.Parser.Composition

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness
open R2ConcreteSuppliers

namespace R2CompactControls

def nthQuestion (input : String) (skip : Nat) : Option ScannerState :=
  let rec go (s : ScannerState) (fuel remaining : Nat) : Option ScannerState :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match scanNextToken s with
      | .ok (some next) =>
        if next.tokens.size > s.tokens.size && next.tokens.back?.any (fun t => t.val == .key)
        then match remaining with
          | 0 => some next
          | k + 1 => go next fuel k
        else go next fuel remaining
      | _ => none
  go ((ScannerState.mk' input).emit .streamStart) ((input.utf8ByteSize + 1) * 4) skip

def questionState (input : String) (skip : Nat) : ScannerState :=
  (nthQuestion input skip).getD (ScannerState.mk' input)

example : (nthQuestion input6 3).isSome = true := by decide +kernel
lemma marks0 : markedCols (questionState input6 0) = [0] := by decide +kernel
lemma marks1 : markedCols (questionState input6 1) = [0,2] := by decide +kernel
lemma marks2 : markedCols (questionState input6 2) = [0,2,4] := by decide +kernel
lemma marks3 : markedCols (questionState input6 3) = [0,2,4,6] := by decide +kernel
example : (questionState input6 0).offset = 1 ∧ (questionState input6 0).col = 1 := by decide +kernel
example : (questionState input6 1).offset = 3 ∧ (questionState input6 1).col = 3 := by decide +kernel
example : (questionState input6 2).offset = 5 ∧ (questionState input6 2).col = 5 := by decide +kernel
example : (questionState input6 3).offset = 7 ∧ (questionState input6 3).col = 7 := by decide +kernel
example : markedCols (ScannerState.mk' "") = [] := by decide +kernel
example : (nthQuestion "" 0).isNone := by decide +kernel

-- Public parser controls are executable observations, separate from grammar proofs.
#guard (L4YAML.TokenParser.parseYaml "? a\n: b\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? a\n  : b\n: c\n").isOk
#guard (L4YAML.TokenParser.parseYaml input6).isOk
#guard (L4YAML.TokenParser.parseYaml "? ? a\n  : b\n  ? c\n  : d\n: e\n").isOk
#guard (L4YAML.TokenParser.parseYaml "? ? a\n: e\n").isOk

end R2CompactControls
