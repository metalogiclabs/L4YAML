import Research.R2CompactSlot.Controls

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness

namespace R2SequenceControls

def nthDash (input : String) (skip : Nat) : Option ScannerState :=
  let rec go (s : ScannerState) (fuel remaining : Nat) : Option ScannerState :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match scanNextToken s with
      | .ok (some next) =>
        if next.tokens.size > s.tokens.size && next.tokens.back?.any (fun t => t.val == .blockEntry)
        then match remaining with
          | 0 => some next
          | k + 1 => go next fuel k
        else go next fuel remaining
      | _ => none
  go ((ScannerState.mk' input).emit .streamStart) ((input.utf8ByteSize + 1) * 4) skip

def dashState (input : String) (skip : Nat) : ScannerState :=
  (nthDash input skip).getD (ScannerState.mk' input)

def siblings : String := "? - a\n  - b\n: c\n"
def compactQuestion : String := "? - ? a\n    : b\n: c\n"
def nested : String := "? -\n    - a\n: b\n"
def compact : String := "? - - a\n    - b\n  - c\n: d\n"
def ancestors : String := "? ? - - a\n      - b\n    - c\n  : d\n: e\n"

example : (nthDash "" 0).isNone := by decide +kernel
example : (nthDash "- a\n- b\n" 0).isSome = true := by decide +kernel
example : (dashState "- a\n- b\n" 0).offset = 1 := by decide +kernel
example : markedCols (dashState "- a\n- b\n" 0) = [] := by decide +kernel
lemma siblingsMarks : markedCols (dashState siblings 0) = [0] := by decide +kernel
lemma questionMarks : markedCols (dashState compactQuestion 0) = [0] := by decide +kernel
example : (dashState compactQuestion 0).offset = 3 ∧ (dashState compactQuestion 0).col = 3 := by decide +kernel
example : (nthDash nested 1).isSome = true := by decide +kernel
example : markedCols (dashState nested 1) = [0] := by decide +kernel
example : (nthDash compact 1).isSome = true := by decide +kernel
example : markedCols (dashState compact 1) = [0] := by decide +kernel
example : markedCols (dashState ancestors 1) = [0,2] := by decide +kernel

#guard (L4YAML.TokenParser.parseYaml siblings).isOk
#guard (L4YAML.TokenParser.parseYaml compactQuestion).isOk
#guard (L4YAML.TokenParser.parseYaml nested).isOk
#guard (L4YAML.TokenParser.parseYaml compact).isOk
#guard (L4YAML.TokenParser.parseYaml ancestors).isOk
#guard (L4YAML.TokenParser.parseYaml "? -\n  - a\n: b\n").isOk

end R2SequenceControls
