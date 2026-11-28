module
public import L4YAML.Proofs.Scanner.ColFloor

@[expose] public section MapOwnershipControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner

namespace R2MapOwnership

def Maps (s : ScannerState) : Prop :=
  ∀ (i l : Nat), s.pendingKeys[i]? = some (some l) →
    ∃ entry : IndentEntry, s.indents[i]? = some entry ∧ entry.isSequence = false

def check (s : ScannerState) : Bool :=
  (List.range s.pendingKeys.size).all fun i =>
    match s.pendingKeys[i]? with
    | some (some _) => (s.indents[i]?).any fun e => !e.isSequence
    | _ => true

def checkSteps : Nat → ScannerState → Bool
  | 0, s => check s
  | fuel+1, s => check s && match scanNextToken s with
      | .ok (some next) => checkSteps fuel next
      | _ => true

def inputs : List String := ["", "? a\n: b\n", "? ? a\n  : b\n: c\n",
  "? - ? a\n    : b\n  - c\n: d\n", "? - ? a\n  - c\n: d\n",
  "? [a, {b: c}]\n: d\n", "? &p !foo a\n: b\n", "? |\n  a\n: b\n",
  "---\n? a\n: b\n...\n---\n? c\n: d\n", "%YAML 1.2\n---\n? a\n: b\n",
  "%TAG !e! tag:example.com,2026:\n---\n? !e!t a\n: b\n", "- a\n? b\n: c\n",
  "? é\n: 雨\n", "?\tbad\n: value\n", "[? a: b, c]\n", "? {a: [b]}\n: c\n"]

#guard inputs.all fun input => checkSteps 0 ((ScannerState.mk' input).emit .streamStart)
#guard inputs.all fun input => checkSteps 1 ((ScannerState.mk' input).emit .streamStart)
#guard inputs.all fun input => checkSteps 2 ((ScannerState.mk' input).emit .streamStart)
#guard inputs.all fun input => checkSteps 80 ((ScannerState.mk' input).emit .streamStart)

def bad : ScannerState := { ScannerState.mk' "? a\n: b\n" with
  indents := #[{column := -1, isSequence := false}, {column := 0, isSequence := true}],
  pendingKeys := #[none, some 0] }

#guard check bad = false

end R2MapOwnership

end MapOwnershipControls
