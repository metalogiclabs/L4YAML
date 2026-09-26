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


/-! ## §4 The same family SWEPT, and the branch it prices (DOCS item 264)

The columns above are hand-typed, and a hand-typed knob chooses the answer (§9).
This section walks the landing column instead and lets the machine name the
**turnover** — the least column the scanner accepts — at every combination of
three enclosing contexts, four park kinds, both flow-open characters and four
park indents.

**Why it is worth sweeping a family already pinned.**  `accum_flow_open_depth0`
spends β.5's `dropClose` at exactly one place, `have drop_ride`, and three LIVE
arms take it — `pendingProps`, `pendingBlock` and `pendingMapValue`, one each,
all on the run-end half of this under-run:

    rcases h_ur with ⟨j, sx, hj, h_ind, _h_ws2, h_end | h_tab⟩
    · exact drop_ride                              -- §4's subject
    · exact (flowOpen_underRunTab_refuted …).elim  -- §3's half, already REFUTED

So this family is not an audit of the scanner — it is the price of the one
library proof β.5 breaks that is neither a dead branch nor the escape.  The
source says of those three rides that "no accepted scan ever consults" them; §4
is that sentence measured instead of asserted, and what it measures is that the
run-end half is refutable exactly where the tab half already is.

**The props park is why a sweep was needed and not another column.**  Its
turnover does not track its own column: an anchor at column 3 takes a flow open
at column 1.  `pendingProps.h_floor : IndentFloor sc n` carries the floor of the
context the run stands IN, not the anchor's, so the boundary sits at 1 from
indent 1 rightwards — and a grid varying only the park's own column would have
read that as an under-run being accepted. -/

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok a, .ok b => a == b
  | _, _ => false

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- A park of the given kind at indent `p`, a break, then `q` spaces and a
    depth-0 flow open.  `outer` supplies the indent when `p` is nonzero, and it
    is varied because a boundary that moved with the enclosing construct would
    be a fact about that construct rather than about the floor. -/
private def mk (outer kind : String) (p q : Nat) (op : String) : String :=
  let pre := match outer, p with
    | _, 0 => ""
    | "map", _ => "w:\n"
    | "seq", _ => "-\n"
    | _, _ => "? w\n: v\nz:\n"
  let body := match kind with
    | "mapValue" => spaces p ++ "k:"
    | "block" => spaces p ++ "-"
    | "qmark" => spaces p ++ "?"
    | _ => spaces p ++ "&a"
  pre ++ body ++ "\n" ++ spaces q ++ op ++ "\n"

private def outers : List String := ["map", "seq", "doc"]
private def kinds : List String := ["mapValue", "block", "qmark", "props"]
private def opens : List String := ["[1]", "{a: b}"]
private def indents : List Nat := [0, 1, 2, 3]
private def columns : List Nat := [0, 1, 2, 3, 4, 5]

/-- **The park's floor, as a model of this grid.**  Three of the four kinds ARE
    the level they stand at, so their floor is one past their own column.  The
    props run is not: it carries the floor of the context it stands in, which
    this grid nests at 1.  Pinning the turnover against a MODEL rather than
    against a list of numbers is what makes the reading a law — and a wrong
    model fails the census rather than sliding it. -/
private def floorOf (kind : String) (p : Nat) : Nat :=
  if kind == "props" then min p 1 else p + 1

/-- One walk of the grid: `(cells, rows with a single boundary, turnover = the
    floor, accepted BELOW the floor, accepted AT the floor)`.

    The third and fourth are the same reading taken two ways, so neither can
    pass vacuously: the fourth counts accepted cells left of the floor directly
    and must be **zero**, and the fifth counts the floor cells themselves and
    must be all of them — a zero over a grid that never reached the boundary
    would be a coverage report (§9). -/
private def sweep : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cells := 0
  let mut clean := 0
  let mut atFloorTurn := 0
  let mut belowOk := 0
  let mut atFloorOk := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          cells := cells + 1
          let n := floorOf kind p
          let row := columns.map (fun q => accepts (mk outer kind p q op))
          -- monotone in `q` with ONE boundary: a row that accepts, refuses and
          -- accepts again has no turnover to speak of.
          if !((row.dropWhile (· == false)).any (· == false)) then
            clean := clean + 1
          if (columns.zip row |>.filter (·.2) |>.map (·.1)).head? == some n then
            atFloorTurn := atFloorTurn + 1
          for (q, ok) in columns.zip row do
            if ok && q < n then belowOk := belowOk + 1
            if ok && q == n then atFloorOk := atFloorOk + 1
  return (cells, clean, atFloorTurn, belowOk, atFloorOk)

/- **Ninety-six cells, every one with a single boundary, and the boundary is
    the floor.**  No accepted scan in the grid lands a depth-0 flow open
    strictly left of the park's floor — which is the branch `drop_ride` is
    spent on — and all ninety-six floor cells are accepted, so the grid
    straddles the boundary rather than sitting to one side of it. -/
#guard sweep == (96, 96, 96, 0, 96)

/- The props cell the hand-typed columns above do not reach: the anchor stands
    at column 3 and the open it takes is at column 1, two columns to its LEFT
    and accepted, because the floor the park carries is the enclosing
    mapping's. -/
#guard emits (mk "map" "props" 3 1 "[1]")
  ["+STR", "+DOC", "+MAP", "=VAL :w", "+SEQ [] &a", "=VAL :1", "-SEQ", "-MAP",
   "-DOC", "-STR"]

/- …and one column further left is the under-run, refused at the EOF gate —
    the "deferred floor" reading, §1's. -/
#guard errAt (mk "map" "props" 3 0 "[1]") == some (2, 0)

end L4YAML.Tests.Guards.ScannerFlowOpenUnderRun
