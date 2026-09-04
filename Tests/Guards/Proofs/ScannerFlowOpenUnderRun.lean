import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A flow open below the pending's index is a scanner refusal (DOCS item 66)

Item 46 left one deferral at the depth-0 flow open: the landing that under-runs
`s-indent(n)` on the OPEN itself, which no `[70] s-separate-lines(n)` derives.
Item 66 refuses it instead of riding `scannerDrop`, and the refusal is §8.1's
own — `scanNextToken_checkBlockFlowIndent`, the single check `scanNextToken`
runs between the structural dispatch and the flow one.

Two facts make the arithmetic work, and both are pinned below.

* §1 **the floor is exact.**  A `[` at or left of the enclosing block
  collection's indent is `underIndentedFlowContent`; one column past it reads.
  The pending's own floor (`n ≤ currentIndent + 1`) turns the under-run's
  `j < n` into `j ≤ currentIndent`, which is that condition.
* §2 **and the landing that matches no open level never gets that far**:
  preprocessing's own trailing-content check refuses it while unwinding.  So
  the two together cover every column below the index — §1 where the landing
  lands on a level, §2 where it lands between two.
* §3 **the TAB half is §6.1's** (item 64's `LandingTabFacts`): a tab in the
  landing's indent run is `tabInIndentation`, at every column at or left of
  the floor.

ZERO runtime edits: every pin below behaved this way before item 66 too. -/

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

private def trailingAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.trailingContent l c) => some (l, c)
  | _ => none

-- §1/§2 A SEQUENCE entry pending at index 2 (`k:⏎  -`).  Every column below
-- the index is refused, and the two refusals alternate with the levels: 0 is
-- the enclosing mapping's, 1 lands between two levels, 2 is the sequence's.
#guard errAt "k:\n  -\n[1]\n" == some (2, 0)
#guard trailingAt "k:\n  -\n [1]\n" == some (2, 1)
#guard errAt "k:\n  -\n  [1]\n" == some (2, 2)
#guard emits "k:\n  -\n   [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- …and one level deeper, where the alternation runs four columns.
#guard errAt "a:\n  b:\n    -\n[1]\n" == some (3, 0)
#guard trailingAt "a:\n  b:\n    -\n [1]\n" == some (3, 1)
#guard errAt "a:\n  b:\n    -\n  [1]\n" == some (3, 2)
#guard trailingAt "a:\n  b:\n    -\n   [1]\n" == some (3, 3)
#guard errAt "a:\n  b:\n    -\n    [1]\n" == some (3, 4)
#guard refuses "a:\n  b:\n    -\n[1]\n"

-- The same for a mapping VALUE pending (`k:⏎  a:`) and for a held property
-- run (`k:⏎  b:⏎    &x`) — the other two parks that open the stack at their
-- own index.
#guard errAt "k:\n  a:\n[1]\n" == some (2, 0)
#guard trailingAt "k:\n  a:\n [1]\n" == some (2, 1)
#guard errAt "k:\n  b:\n    &x\n  [1]\n" == some (3, 2)

-- §1's boundary at the root, where the floor is the document's own: a `[` at
-- column 0 under a mapping at column 0 is refused, one column past it reads.
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
