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



/-! ## §5 Where each refusal actually happens, and what that costs (DOCS item 265)

§4 measured that no accepted scan lands the open below the park's floor.  That
is a statement about the SCANNER; the proof obligation it was measured for is
`accum_flow_open_depth0`'s, and there the question is sharper: *is the refusal
available at the step the arm is proving?*  A branch the runtime refuses five
steps downstream is still a branch the step lemma has to build.

So this section walks the same grid one reading further in.  For every landing
column strictly below the park's floor it drives `scanNextToken` itself and
records two things: whether the flow OPEN is ever dispatched, and — when it is
— how far past that dispatch the scan dies and at which gate.

What it reads splits the family in two, and only one part is the arm's to
refute:

* **54 columns never reach the lemma.**  `scanNextToken_preprocess` refuses
  them while unwinding, so `h_preprocess : … = .ok (some (s_prep, c))` is
  already a contradiction and no arm is entered.
* **144 columns dispatch the open** and die three or five steps later, at one
  of the two gates that guard a landing: §8.1's floor read on a closed
  collection (90) and §9.2's dangling run (54).  Both gates also run at the
  open's own step — on a state where the collection is not yet closed, so both
  say `.ok` there.  `h_dn` and `h_bare` are those readings AT THE OPEN, which
  is why carrying them buys nothing here: they are the right checks at the
  wrong state.

`deathShape` then reads what the gate is looking at when it fires, because that
is the fact a carrier would have to deliver from the open: at every one of the
144 the collection has closed, the last real token is its flow close, and the
open's column is still on the indent stack.  One carried fact, not two — the
two gates partition the 144 by `offersNodeSlot` alone, with no overlap and no
remainder. -/

private def start (input : String) : Scanner.ScannerState :=
  let s := Scanner.ScannerState.mk' input
  let s := s.emit .streamStart
  match s.peek? with
  | some '﻿' => s.consumeBOM
  | _ => s

/-- `(open dispatched?, steps from the open to the death, the gate that fired)`
    for one input, driving `scanNextToken` directly. -/
private def walk (input : String) : Bool × Nat × String := Id.run do
  let mut s := start input
  let mut i : Nat := 0
  let mut openStep : Option Nat := none
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    let d := i - openStep.getD i
    match Scanner.scanNextToken s with
    | .error _ =>
      -- inside the step: preprocessing is the only gate that can refuse
      -- before the open is dispatched
      match Scanner.scanNextToken_preprocess s with
      | .error _ => return (openStep.isSome, d, "step:preprocess")
      | _ => return (openStep.isSome, d, "step:later")
    | .ok none =>
      if s.flowLevel > 0 then return (openStep.isSome, d, "eof:unterminated")
      match Scanner.scanLoop_checkDanglingNode s with
      | .error _ => return (openStep.isSome, d, "eof:dangling")
      | .ok _ =>
        match Scanner.scanLoop_checkFlowValueIndent s with
        | .error _ => return (openStep.isSome, d, "eof:floor")
        | .ok _ => return (openStep.isSome, d, "ACCEPT")
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 && openStep.isNone then
        openStep := some i
      s := s'
      i := i + 1
  return (openStep.isSome, 0, "FUEL")

/-- `(columns below a floor, never dispatched, of those refused by
    PREPROCESSING, dispatched, dispatched dying at §8.1's floor, dispatched
    dying at §9.2's dangling run)`.

    The second and third are the same count taken two ways: a column that
    never dispatches the open must be refused by the one gate that runs before
    the dispatch, and if it were refused anywhere else the arm's
    `h_preprocess` would not reach it. -/
private def dispatchSweep : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cols := 0
  let mut nd := 0
  let mut ndPre := 0
  let mut disp := 0
  let mut floorDeaths := 0
  let mut danglingDeaths := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            cols := cols + 1
            let (d, _, w) := walk (mk outer kind p q op)
            if d then
              disp := disp + 1
              if w == "eof:floor" then floorDeaths := floorDeaths + 1
              if w == "eof:dangling" then danglingDeaths := danglingDeaths + 1
            else
              nd := nd + 1
              if w == "step:preprocess" then ndPre := ndPre + 1
  return (cols, nd, ndPre, disp, floorDeaths, danglingDeaths)

#guard dispatchSweep == (198, 54, 54, 144, 90, 54)

/-- The distinct distances, in scanner steps, from the open's dispatch to the
    death.  Neither is zero, which is the whole finding: there is no column at
    which the open's OWN step refuses. -/
private def distances : List Nat := Id.run do
  let mut ds : List Nat := []
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let (d, n, _) := walk (mk outer kind p q op)
            if d && !ds.contains n then ds := ds ++ [n]
  return ds.mergeSort (· ≤ ·)

#guard distances == [3, 5]

/-- The state the gate is reading when it fires, over the 144 that dispatch:
    `(rows, collection closed, last real token is its flow close, the open's
    column still on the indent stack, exactly one of the two readings fires)`.
    All five must agree, and the fifth is what says the two gates partition
    the family rather than merely covering it. -/
private def deathState (input : String) : Option Scanner.ScannerState := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ => return some s
    | .ok none => return some s
    | .ok (some s') => s := s'
  return none

private def deathShape : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut closed := 0
  let mut lastClose := 0
  let mut colIn := 0
  let mut oneReading := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            let (d, _, _) := walk inp
            if !d then continue
            match deathState inp with
            | none => pure ()
            | some s =>
              rows := rows + 1
              if s.flowLevel == 0 then closed := closed + 1
              match Scanner.prevRealIdx? s.tokens s.tokens.size with
              | some i => if s.tokens[i]!.val.isFlowClose then lastClose := lastClose + 1
              | none => pure ()
              if s.indents.any (fun e => e.column == (q : Int)) then colIn := colIn + 1
              let uf := (Scanner.underIndentedFlowValuePos? s).isSome
              let dn := (Scanner.danglingNodePos? s).isSome
              if (uf && !dn) || (!uf && dn) then oneReading := oneReading + 1
  return (rows, closed, lastClose, colIn, oneReading)

#guard deathShape == (144, 144, 144, 144, 144)

/-- **The grid ends at the open, and that is itself a knob** (§9).  With a
    sibling line after the open's, the same columns refuse in the same two
    classes and nothing is accepted that was not accepted before.
    `(columns, accepted, never dispatched, dispatched, deaths at a MID-STREAM
    gate)`.

    The fifth count is what makes this a second reading rather than a copy of
    `dispatchSweep`: without the sibling line every death is at an end-of-input
    gate and it reads zero, so a pin that omitted it would hold whether or not
    a tail was ever appended. -/
private def tailSweep : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cols := 0
  let mut acc := 0
  let mut nd := 0
  let mut disp := 0
  let mut mid := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            cols := cols + 1
            let (d, _, w) := walk (mk outer kind p q op ++ "zz: 9\n")
            if w == "ACCEPT" then acc := acc + 1
            if w == "step:later" then mid := mid + 1
            if d then disp := disp + 1 else nd := nd + 1
  return (cols, acc, nd, disp, mid)

#guard tailSweep == (198, 0, 54, 144, 144)


/-! ## §6 What the carrier costs, and who pays it (DOCS item 266)

§5 showed the run-end half is FALSE and not LOCALLY false: the gates that kill
the input run three to five steps past the open, so no hypothesis of
`accum_flow_open_depth0` can refute the branch and what it costs is a CARRIER.
§10 prices a missing carrier by the PRODUCERS it touches, and this section is
the half of that price the runtime decides.  The other half —
`passenger=7 heavy=7 prop=8 consumer=1 gate=1`, pinned below — is
`scripts/carrier_price.py`.

**The transport already exists.**  `ParkAnchor sc0 s d` runs a fact from a
depth-0 flow OPEN to its CLOSE and is spent there by `ParkAnchor.dangling_eq`,
whose premises are §5's `deathShape` component for component: prefix agreement,
`s_cl.indents = s_bc.indents`, `s_cl.inFlow = false`, the last real token at the
base open's index, and that token a flow close.  So the question is not what to
build but what the existing transport refuses to carry.

Three readings answer it.

* **The park is forced.**  `carrierCore` evaluates the anchor's four transport
  fields at the death state against each candidate park.  Against
  preprocessing's state all four hold at all 144; against the state the step
  began from the hold NEVER resolves, because preprocessing's own pushes sit
  between the two arrays.  There is one park, and it is not the one the
  existing anchor uses.
* **At that park the carrier is a PASSENGER.**  `carrierPark`: preprocessing's
  cursor column IS the open's column, at all 144 — so "the open's column stands
  on the indent stack" is a fact about the park ALONE, with no reference to the
  state it is transported to, and every transport lemma carries it for free.
  At the other park the same membership holds but the column is not the park's,
  which is the difference between a passenger and a premise.
* **What blocks the existing anchor is one field.**  `anchorProp`: `parkProp`
  ("the park's last real token is a node property") holds at 18 of the 144, and
  it is a pure passenger in every transport lemma — read by the genesis and by
  the spend, by nothing in between.

And `preLaw` names the carrier's source.  Over all 198 columns, preprocessing
accepts a landing out of flow exactly when its column stands on the indent
stack: the 54 it refuses are the 54 whose column stands nowhere, and the 144 it
accepts all have it.  The datum is preprocessing's own law, one production over
from `FlowIndentStable.preprocess_indents_of_inFlow` — not a field threaded
through the pending-state invariant. -/

private def openTriple (input : String) :
    Option (Scanner.ScannerState × Scanner.ScannerState × Scanner.ScannerState) := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ => return none
    | .ok none => return none
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 then
        match Scanner.scanNextToken_preprocess s with
        | .ok (some (sp, _)) => return some (s, sp, s')
        | _ => return none
      s := s'
  return none

/-- The column of the bracket the open pushed, read back off the array. -/
private def openColOf (s' : Scanner.ScannerState) : Option Nat :=
  match Scanner.prevRealIdx? s'.tokens s'.tokens.size with
  | some i => if s'.tokens[i]!.val.isFlowOpen then some s'.tokens[i]!.pos.col else none
  | none => none

private def hasCol (s : Scanner.ScannerState) (c : Nat) : Bool :=
  s.indents.any (fun e => e.column == (c : Int))

/-- `(rows, the open's column is the STEP state's cursor column, it stands on
    that state's indent stack, it is PREPROCESSING's cursor column, it stands on
    preprocessing's stack)`.

    The second must be zero and the fourth all of them: that is what says the
    carrier is a passenger at one park and not at the other, rather than a
    membership fact that happens to hold at both. -/
private def carrierPark : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut scCol := 0
  let mut scMem := 0
  let mut spCol := 0
  let mut spMem := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, s') =>
              match openColOf s' with
              | none => pure ()
              | some c =>
                rows := rows + 1
                if sc.col == c then scCol := scCol + 1
                if hasCol sc c then scMem := scMem + 1
                if sp.col == c then spCol := spCol + 1
                if hasCol sp c then spMem := spMem + 1
  return (rows, scCol, scMem, spCol, spMem)

#guard carrierPark == (144, 0, 144, 144, 144)

/-- `ParkAnchor`'s four transport fields at the death state, against BOTH
    candidate parks: `(rows, below, held, ind, parkFlow — all at preprocessing's
    state; the rows where `parkProp` holds THERE too; then held and ind at the
    step's state)`.

    The last two are the discrimination: an anchor parked where the existing one
    parks never holds its open, so the park is forced by the runtime and not
    chosen.  A sixth count for "all four at once" would read 144 whatever the
    scanner did, since each of the four already does — so the sixth is the
    overlap with the EXISTING anchor instead, which is the only reading of this
    family that is not implied by the five beside it. -/
private def carrierCore : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut below := 0
  let mut held := 0
  let mut ind := 0
  let mut pflow := 0
  let mut alsoProp := 0
  let mut heldSc := 0
  let mut indSc := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, deathState inp with
            | some (sc, sp, _), some s =>
              rows := rows + 1
              let lastOpen : Nat → Bool := fun n =>
                match Scanner.prevRealIdx? s.tokens s.tokens.size with
                | some i => Scanner.flowOpenIdx? s.tokens i == some n
                | none => false
              let b := (List.range sp.tokens.size).all (fun j => s.tokens[j]! == sp.tokens[j]!)
              let h := lastOpen sp.tokens.size
              let i2 := s.indents == sp.indents
              let prop := match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
                | some k => sp.tokens[k]!.val.isNodeProperty
                | none => false
              if b then below := below + 1
              if h then held := held + 1
              if i2 then ind := ind + 1
              if sp.inFlow == false then pflow := pflow + 1
              if b && h && i2 && sp.inFlow == false && prop then alsoProp := alsoProp + 1
              if lastOpen sc.tokens.size then heldSc := heldSc + 1
              if s.indents == sc.indents then indSc := indSc + 1
            | _, _ => pure ()
  return (rows, below, held, ind, pflow, alsoProp, heldSc, indSc)

#guard carrierCore == (144, 144, 144, 144, 144, 18, 0, 90)

/-- `(rows, the park's last real token is a node PROPERTY, the step's array is
    preprocessing's, the step's indent stack is preprocessing's)`.

    The second is what `ParkAnchor.parkProp` asks and it is 18 of 144 — the
    props cells alone.  The third is zero at every landing: preprocessing always
    writes, which is the same fact `carrierCore`'s hold reads from the other
    side.  The fourth is the unwind, and it is exactly the 90 that §8.1 kills. -/
private def anchorProp : Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut prop := 0
  let mut tokEq := 0
  let mut indEq := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            match openTriple (mk outer kind p q op) with
            | none => pure ()
            | some (sc, sp, _) =>
              rows := rows + 1
              match Scanner.prevRealIdx? sp.tokens sp.tokens.size with
              | some k => if sp.tokens[k]!.val.isNodeProperty then prop := prop + 1
              | none => pure ()
              if sc.tokens.size == sp.tokens.size then tokEq := tokEq + 1
              if sc.indents == sp.indents then indEq := indEq + 1
  return (rows, prop, tokEq, indEq)

#guard anchorProp == (144, 18, 0, 90)

/-- `offersNodeSlot` read exactly as `underIndentedFlowValuePos?` reads it, at
    the death state.

    The close test cannot refuse a cell of this grid — §5's `deathShape` pins
    the last real token as the flow close at all 144 — so it is here because the
    definition MIRRORS the gate, not because it discriminates.  Deleting it
    moves no count, which the perturbation harness asserts rather than
    discovers. -/
private def offersAtDeath (s : Scanner.ScannerState) : Bool :=
  match Scanner.prevRealIdx? s.tokens s.tokens.size with
  | none => false
  | some i =>
    if !(s.tokens[i]!.val.isFlowClose) then false
    else
      match Scanner.flowOpenIdx? s.tokens i with
      | none => false
      | some o =>
        match Scanner.prevRealIdx? s.tokens (Scanner.propsRunStart s.tokens o) with
        | some j => s.tokens[j]!.val.offersNodeSlot
        | none => false

/-- `(rows, the slot OFFERS, BOTH gates fire, offers ∧ §8.1 fires, ¬offers ∧
    §9.2 fires, the hold resolves to preprocessing's array end)`.

    §5 read the 90/54 split off the gate that fired; this reads it off the token
    array instead, and the two agree cell for cell — which is what says
    `offersNodeSlot` IS the partition and not a correlate of it.  The third
    count is the half §5 could not state: its `oneReading` counts an exclusive
    or, which a cell firing NEITHER gate would also fail, so the overlap is
    counted here directly and must be zero. -/
private def slotSplit : Nat × Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut rows := 0
  let mut off := 0
  let mut both := 0
  let mut offFloor := 0
  let mut noffDang := 0
  let mut openIdx := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            let inp := mk outer kind p q op
            match openTriple inp, deathState inp with
            | some (_, sp, _), some s =>
              rows := rows + 1
              let o := offersAtDeath s
              if o then off := off + 1
              if (Scanner.underIndentedFlowValuePos? s).isSome
                  && (Scanner.danglingNodePos? s).isSome then both := both + 1
              if o && (Scanner.underIndentedFlowValuePos? s).isSome then
                offFloor := offFloor + 1
              if !o && (Scanner.danglingNodePos? s).isSome then
                noffDang := noffDang + 1
              match Scanner.prevRealIdx? s.tokens s.tokens.size with
              | some i =>
                if Scanner.flowOpenIdx? s.tokens i == some sp.tokens.size then
                  openIdx := openIdx + 1
              | none => pure ()
            | _, _ => pure ()
  return (rows, off, both, offFloor, noffDang, openIdx)

#guard slotSplit == (144, 90, 0, 90, 54, 144)

/-- The state the landing step begins from, and whether preprocessing accepts
    it — the one reading that has to be taken on the columns the scan REFUSES,
    where no later state exists. -/
private def landingStep (input : String) : Option (Scanner.ScannerState × Bool) := Id.run do
  let mut s := start input
  let mut fuel := input.utf8ByteSize * 4 + 8
  while fuel > 0 do
    fuel := fuel - 1
    match Scanner.scanNextToken s with
    | .error _ =>
      match Scanner.scanNextToken_preprocess s with
      | .error _ => return some (s, false)
      | _ => return some (s, true)
    | .ok none => return none
    | .ok (some s') =>
      if s.flowLevel == 0 && s'.flowLevel == 1 then return some (s, true)
      s := s'
  return none

/-- **The carrier's SOURCE, over all 198 columns**: `(columns, preprocess
    refuses, of those the landing's column stands on NO level, preprocess
    accepts, of those it stands on one)`.

    Both directions, because one of them alone is a coverage report: the refused
    columns are refused BECAUSE the column matches no level, and every accepted
    one matches.

    `columns = refuses + accepts` is a READING here, not an identity: a cell
    whose scan runs to the end of the stream without reaching the landing at all
    is counted in the first and in neither of the other two.  What `198 = 54 +
    144` says is that no cell of this grid does that. -/
private def preLaw : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut cols := 0
  let mut bad := 0
  let mut badOut := 0
  let mut good := 0
  let mut goodIn := 0
  for outer in outers do
    for kind in kinds do
      for op in opens do
        for p in indents do
          for q in List.range (floorOf kind p) do
            cols := cols + 1
            match landingStep (mk outer kind p q op) with
            | none => pure ()
            | some (s, ok) =>
              if ok then
                good := good + 1
                if hasCol s q then goodIn := goodIn + 1
              else
                bad := bad + 1
                if !hasCol s q then badOut := badOut + 1
  return (cols, bad, badOut, good, goodIn)

#guard preLaw == (198, 54, 54, 144, 144)

/-- What `scripts/carrier_price.py` reads by editing `StreamAccum.lean` and
    counting the declarations each edit breaks.

    Five probes, five rings.  `passenger` and `heavy` add the carrier to
    `ParkAnchor` as a field — the first stated over the park alone, the second
    over the array — and they read the SAME census, which is the reading worth
    keeping: an arity flip counts SITES, not work, so it cannot tell a passenger
    from a premise and the runtime pins above are what do.  `prop` deletes
    `parkProp` and adds one declaration to the seven: the spend.  `consumer` and
    `gate` are the two rings below, and each is a single declaration. -/
def expectedCarrierPrice : String :=
  "passenger=7 heavy=7 prop=8 consumer=1 gate=1"

end L4YAML.Tests.Guards.ScannerFlowOpenUnderRun
