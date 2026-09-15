import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A flow open below the pending's index is refused at the gate (DOCS items 66, 172)

Item 46 left one deferral at the depth-0 flow open: the landing that under-runs
`s-indent(n)` on the OPEN itself, which no `[70] s-separate-lines(n)` derives.
Item 66 refused it at the open; item 172 moved §8.1's floor to the CLOSE
(a flow open at a level's column may be the level's next implicit KEY, so
key-vs-value is only decidable there), and the under-run family now refuses at
the break/EOF gate, by whichever of the two gate readings owns the landing:

* §1 **at a level whose slot still OFFERS a node** — the `-`'s own column, a
  props park's floor, the root value slot — the deferred floor refuses as
  `underIndentedFlowContent` at the OPEN's position: the collection stood in
  the awaited slot and no `:` resolved it (`underIndentedFlowValuePos?`,
  `[96]`-transparent through the run in front of the open).
* §1' **where the landing DEDENTS past the awaiting level**, preprocessing's
  unwind closes it (`blockEnd`), the slot holder no longer offers, and the
  same landing is §9.2's dangling node — `invalidBareDocument` at the open's
  position, the constructor the scalar twin gets.
* §2 **the landing that matches no open level never gets that far**:
  preprocessing's own trailing-content check refuses it while unwinding.  So
  the readings together cover every column below the index.
* §3 **the TAB half is §6.1's** (item 64's `LandingTabFacts`): a tab in the
  landing's indent run is `tabInIndentation`, at every column at or left of
  the floor. -/

namespace L4YAML.Tests.Guards.ScannerFlowOpenUnderRun

open L4YAML

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def errAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.underIndentedFlowContent l c) => some (l, c)
  | _ => none

private def bareAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.invalidBareDocument l c) => some (l, c)
  | _ => none

private def trailingAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.trailingContent l c) => some (l, c)
  | _ => none

-- §1/§1'/§2 A SEQUENCE entry pending at index 2 (`k:⏎  -`).  Every column
-- below the index is refused, and the refusals alternate with the levels:
-- 0 dedents past the sequence (§1', the unwind's `blockEnd` de-offers the
-- slot), 1 lands between two levels (§2), 2 is the sequence's own — the
-- offered slot, the deferred floor's reading at the open's position (§1).
#guard bareAt "k:\n  -\n[1]\n" == some (2, 0)
#guard trailingAt "k:\n  -\n [1]\n" == some (2, 1)
#guard errAt "k:\n  -\n  [1]\n" == some (2, 2)
#guard emits "k:\n  -\n   [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- …and one level deeper, where the alternation runs four columns: 0 and 2
-- dedent past the sequence (§1'), 1 and 3 land between levels (§2), 4 is the
-- sequence's own offered slot (§1).
#guard bareAt "a:\n  b:\n    -\n[1]\n" == some (3, 0)
#guard trailingAt "a:\n  b:\n    -\n [1]\n" == some (3, 1)
#guard bareAt "a:\n  b:\n    -\n  [1]\n" == some (3, 2)
#guard trailingAt "a:\n  b:\n    -\n   [1]\n" == some (3, 3)
#guard errAt "a:\n  b:\n    -\n    [1]\n" == some (3, 4)
#guard refuses "a:\n  b:\n    -\n[1]\n"

-- The same for a mapping VALUE pending (`k:⏎  a:`) and for a held property
-- run (`k:⏎  b:⏎    &x`) — the other two parks that open the stack at their
-- own index.  The dedent past the value's level is §1'; the props park met at
-- the enclosing level is §1, the run read `[96]`-transparently to the offer.
#guard bareAt "k:\n  a:\n[1]\n" == some (2, 0)
#guard trailingAt "k:\n  a:\n [1]\n" == some (2, 1)
#guard errAt "k:\n  b:\n    &x\n  [1]\n" == some (3, 2)

-- §1's boundary at the root, where the floor is the document's own: a `[` at
-- column 0 in the root value slot is refused at the gate, one column past it
-- reads.  (The KEY half of the same landing — `k:⏎[1]: b` — is the sibling
-- entry now; `StreamFlipRemainderMap` §5 pins it.)
#guard errAt "k:\n[1]\n" == some (1, 0)
#guard emits "k:\n [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "=VAL :1", "-SEQ", "-MAP",
   "-DOC", "-STR"]

-- §3 The TAB half, at every column the floor admits.
#guard refuses "k:\n  -\n\t[1]\n"
#guard refuses "k:\n  -\n \t[1]\n"
#guard refuses "k:\n  a:\n\t[1]\n"
#guard refuses "a:\n  b:\n    -\n  \t[1]\n"

end L4YAML.Tests.Guards.ScannerFlowOpenUnderRun
