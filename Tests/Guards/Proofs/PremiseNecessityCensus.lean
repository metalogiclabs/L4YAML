import Tests.Guards.Proofs.HypothesisReaderCensus

/-!
# The necessity census: a premise that is READ is not thereby NEEDED (item 226)

Item 225 closed with the lane it found and did not spend: **`RELAY` is 1997
binders in `StreamAccum` alone and nothing gates it**, and §5's nine-row
core-terminal shortlist was named "the first place one would look for a premise
that could simply be dropped".  This item went there.  Nothing in that lane is
droppable, the shortlist was an artifact of the walk that made it, and the
premises that ARE free are free for a reason no census of terms can see — the
same reason item 225 proved for `KeyPackPunt` and never applied to the
population it had just measured.

## Three instruments, in the order they were needed

**1.  The walk was pipe-blind.**  Item 213 named `Or.imp` and `Eq.ndrec` PIPES
— they carry a decision and make none — and item 215's `peelPipe` taught the
SUPPLY census to see through them.  The reader census never got that list, so
`uses` stopped at `Or.imp#6` and at an over-applied `Eq.ndrec` and reported the
pipe.  §1 peels them with the SAME `pipeArg`, and nothing is discarded: a
pipe's other arguments go on a side list and are walked, so no occurrence can
vanish into the peel.

Peeled, item 225's pins move and its two disputed sections resolve:

| | item 225 | here |
|---|---|---|
| module tally | `FIELD=154 READ=1016 RELAY=1997 RETURN=48` | `FIELD=172 READ=1052 RELAY=1864 RETURN=127` |
| optional tally | `total=163 ETA=34 READ=85 RELAY=44` | `ETA=34 FIELD=4 READ=85 RELAY=38 RETURN=2` |
| §5's shortlist | 9 rows | **0** — all nine land, two on a LIBRARY elimination |
| `h_ref`'s terminals | 3 | **2** — the third was the pipe |
| §7's two exhibits | `RELAY` / `RELAY` | `RELAY` / **`RETURN`** |

The calibration against item 224's eight REBUILDS is **unchanged**, and so is
`content_dispatch_routed`'s six and the nine-row `UNUSED` lane — so the peel
moves what a pipe was hiding and nothing else.

**2.  The dead-parameter fixpoint** (§5): the least fixpoint of ALIVE over the
relay graph.  A binder is ALIVE if it is eliminated, applied, projected, stored
in a constructor, returned, or named in a later binder's TYPE — that last one
is a check a census does not need and a DROP does — and a relay is ALIVE iff
its target is.  DEAD is therefore a sound under-approximation.  Over every
`Prop` binder of `StreamAccum` and every `_ ∨ True` binder in `L4YAML`, 4266
nodes: **ten are dead and every one of them is `UNUSED`.  The `RELAY` lane has
none.**

**3.  The substitution probe** (`scripts/decline_all_optional.py`): replace a
binder's uses with the canonical inhabitant of its type and rebuild.  For
`A ∨ True` that inhabitant is `Or.inr trivial`, so the probe is available for
the whole optional population — and **all 119 of `StreamAccum`'s optional
premises that live in a tactic proof can be declined AT ONCE, in one build,
with zero errors**, after which Lean's own `unusedVariables` linter names 95 of
them.  The probe's whole content is that it converts the ungated `RELAY` lane
into the gated `UNUSED` one and lets the toolchain answer.

## The rule this item adds

**A premise that is READ is not thereby NEEDED.**  `READ` measures what a proof
DOES with a binder; necessity is a question about the lemma's STATEMENT, and
for `A ∨ True` the statement answers it alone: the type is unconditionally
inhabited, so `opt_premise_buys_nothing` discharges it in one line and all 163
optional contexts — **85 of them `READ`** — buy nothing today.  Item 225 proved
exactly this for `KeyPackPunt` and stopped there.  (**165**, corrected at item
227: two more hide behind `ResumeKeyCtx`, and the lemma covers those too — see
`Tests.Guards.NarrowingWorthCensus` §6.)

## And the ten dead ones are not droppable either

Read in source they are three kinds, and none is a premise carried by accident:

* **class markers, 7.**  `block_dispatch_deferred_stamp_offcol`,
  `…_stamp_nopack` and `…_inline` have ONE call in the body —
  `block_dispatch_deferred …` — and the premise the body does not read is the
  only thing that says which dispatch class the site is in.  Item 187's own
  comment records `_h_park` as placed LAST "so the existing applications'
  positional arguments still bind".  Dropping them would not simplify the
  library; it would delete the taxonomy and merge three lemmas back into one.
* **family uniformity, 2.**  `h_noflow_disp` is a premise of six sibling
  openers and five of them use it; `scanTagDirective_corr`'s `_hcorr` is the
  `*_corr` family's shared leading triple.
* **the conclusion's own binder, 1.**  `flowKeyPack_of_close`'s `intro _` takes
  `sc.simpleKey.possible = true` out of the CONCLUSION, whose shape is fixed by
  the obligation the lemma discharges.

**An underscore silences the linter; it does not justify the premise.**  Seven
of these nine carry one, and the justification is in none of them — it is in
the body's shape, in a sibling's signature, and in the conclusion.

## Nothing is spent, and that is the answer

The 163 optional contexts are the NARROWING SURFACE: items 212–218 built a
supply census precisely to price replacing `∨ True` with the bare premise, and
item 218 recorded that "a `PAY` is an answer about the PROOF, and it does not
promise the site survives a narrowing."  Dropping a vacuous premise today
deletes the slot the narrowing lands in.  The mandate asked which premise could
simply be dropped; the measured answer is that the lane it pointed at has none
and the lane that does is one the plan is holding open on purpose.
-/

namespace Tests.Guards.PremiseNecessityCensus

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus
open Tests.Guards.HypothesisReaderCensus

/-! ## §1  The pipe peel

`pipeArg` is item 214's list and `arityOf` item 215's; neither is re-typed
here.  Two rules, and both keep everything:

* a SATURATED pipe IS its carrier, and the pipe's other arguments go on the
  side list;
* an OVER-APPLIED pipe transports a FUNCTION, so `P … m … x₁ … xₙ` becomes
  `m x₁ … xₙ` (head-beta'd) with the pipe's own arguments on the side list.

The side list is what makes the peel safe: a binder occurring inside the `f` of
`Or.imp f g h` is still walked, so the peel can move a verdict and cannot
invent an `UNUSED`. -/

/-- Peel saturated pipes; `side` collects what the peel stepped over. -/
partial def peelSat (env : Environment) (e : Expr) (side : Array Expr) :
    Expr × Array Expr :=
  match e with
  | .mdata _ b => peelSat env b side
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const g _ =>
          match pipeArg g with
          | some i =>
              if i < args.size && args.size == arityOf env g then
                let side := (List.range args.size).foldl
                  (fun (acc : Array Expr) k => if k == i then acc else acc.push args[k]!) side
                peelSat env args[i]! side
              else (e, side)
          | none => (e, side)
      | _ => (e, side)
  | _ => (e, side)

/-- An over-applied pipe transports a function: rewrite to what it transports
    applied to the trailing arguments. -/
def peelOver (env : Environment) (e : Expr) : Option (Expr × Array Expr) :=
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const g _ =>
      match pipeArg g with
      | some i =>
          let ar := arityOf env g
          if i < args.size && ar < args.size then
            let side := (List.range ar).foldl
              (fun (acc : Array Expr) k => if k == i then acc else acc.push args[k]!) #[]
            some ((mkAppN args[i]! (args.extract ar args.size)).headBeta, side)
          else none
      | none => none
  | _ => none

/-- Item 226's peel, for `usesWith`. -/
def pipePeel (env : Environment) : Peel := fun e =>
  match peelOver env e with
  | some (e', side) => (e', side)
  | none => peelSat env e #[]

def verdictP (env : Environment) (c : Name) (i : Nat) : String :=
  verdictWith (pipePeel env) env c i

def binderUsesP (env : Environment) (c : Name) (i : Nat) : Option (Array Use) :=
  binderUsesWith (pipePeel env) env c i

def chaseP (env : Environment) (fuel : Nat) (c : Name) (i : Nat) : Std.HashSet String :=
  chaseWith (pipePeel env) env fuel {} c i

/-! ## §2  The calibration, and what the peel does NOT move

Item 224's eight rebuild verdicts are still the ground truth, and the peeled
walk reproduces item 225's sixteen rows exactly.  A peel that moved the
calibration would be a peel that changed the answer, not the instrument. -/

run_cmd do
  let env ← getEnv
  let got := expectedCalibration.length
  let rows : List (Name × Nat) :=
    [ (``block_dispatch_deferred, 5), (``block_dispatch_deferred_stamp_offcol, 8),
      (``block_dispatch_deferred_stamp_nopack, 7), (``block_dispatch_deferred_inline, 7),
      (``accum_block_on_closeThenBlock, 17), (``colon_fires_implicit_key, 11),
      (``accum_block_on_pendingContent, 23), (``accum_block_on_pendingBlockContent, 25),
      (``accum_block_on_noPending, 13), (``accum_content_on_noPending, 14),
      (``flowKeyRoute_of_open, 14), (``flowKeyRoute_of_root, 9),
      (``keyctx_of_preprocess, 11), (``landing_or_park_save, 6),
      (``landing_or_park_ska, 6), (``preprocess_flow_thread, 9) ]
  if rows.length != got then
    throwError "the calibration's row count moved: {rows.length} vs {got}"
  let peeled := rows.map (fun (c, i) => verdictP env c i)
  let blind := expectedCalibration.map (fun r => (r.splitOn " ").head!)
  if peeled != blind then
    throwError "the PEEL moved item 224's calibration.\nblind:  {
      String.intercalate " " blind}\npeeled: {String.intercalate " " peeled}"

/-! ## §3  The tallies the peel does move

`constants` is the module's non-internal constant count, generated ones
included: 1124 on Lean v4.33.0, 1123 on v4.34.0, which no longer generates the
derived enum's `FrameTail.toCtorIdx` (see `RelaySupplyCensus.expectedTally`).
Item 257 moves one binder from `FIELD` to `RELAY` under the peel as in the
reader census: `h_mono` at `accum_block_on_closeThenBlock`, handed by the
compact fill's literal to `IndentStackCover.covered_nil_of_top_le`.  Item 259
moves three, as in the reader census: `compact_open_map`'s two new binders
relayed to the same lemma, and its `h_top_in` from `FIELD` to `RELAY` (the
`omega` pinning the slot's top now consumes it): `FIELD` 171 → 170, `RELAY`
1866 → 1869.  Item 267 splits the park anchor into a transport core and two
payloads and adds the carrier's source, which is thirty-four new constants and
thirty-two new binder holders; the peel scores their binders `FIELD` 170 → 171,
`READ` 1057 → 1083, `RELAY` 1869 → 1949 and `RETURN` 127 → 128.  The `UNUSED`
roster is unchanged, which is what says the lanes moved by the new
declarations' own binders and not by a rescoring of an existing one.

    Item 269 restates that source as four declarations where item 267's form is
    two, which is two more constants and two more holders, and the peel scores
    their thirteen `Prop` binders exactly as the reader census does — `READ`
    1083 → 1084 and `RELAY` 1949 → 1951, the one `READ` being
    `preprocess_floor_eq`'s `h_floor`.  That the two classifiers agree on the
    same thirteen is the reading: the peel and the reader differ on what a
    binder is used FOR, and here there is nothing for them to differ about.

    Item 271 adds the under-run's column reading and item 272 the composition
    that spends it, one constant and one holder each: `constants` 1161 → 1163,
    `decls` 981 → 983.  The peel scores their fifteen `Prop` binders the way
    the reader does — `READ` 1084 → 1086, `RELAY` 1951 → 1964 — and the two
    `READ`s are both item 271's, `h_floor` and `hcorr`, each projected.  Item
    272's nine all relay, which is what a composition is. -/

def expectedModuleTallyP : String :=
  "constants=1163 decls=983 eta=369 FIELD=171 READ=1086 RELAY=1964 RETURN=128 UNUSED=9"

def expectedOptTallyP : String :=
  "total=163 ETA=34 FIELD=4 READ=85 RELAY=38 RETURN=2"

run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut names : Array Name := #[]
  for (nm, _) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    names := names.push nm
  let mut tally : Std.HashMap String Nat := {}
  let mut eta := 0
  let mut decls := 0
  let mut unused : Array String := #[]
  for c in names do
    let pbs ← propBinders c
    if pbs.isEmpty then continue
    decls := decls + 1
    for (i, bn) in pbs do
      match binderUsesP env c i with
      | none => eta := eta + 1
      | some us =>
          let d := direct us
          tally := tally.insert d ((tally.getD d 0) + 1)
          if d == "UNUSED" then
            unused := unused.push s!"{c.getString!}#{i} ({shownName bn})"
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"constants={names.size} decls={decls} eta={eta} {body}"
  if got != expectedModuleTallyP then
    throwError "the PEELED module census moved.\nexpected: {
      expectedModuleTallyP}\ngot:      {got}"
  -- the `UNUSED` lane is the one thing the peel must NOT move: it is what the
  -- toolchain already gates, and item 225 pinned it at these nine rows.
  if (unused.qsort (· < ·)).toList != expectedUnused then
    throwError "the peel moved the UNUSED lane.\nexpected:\n{
      String.intercalate "\n" expectedUnused}\ngot:\n{
      String.intercalate "\n" (unused.qsort (· < ·)).toList}"

run_cmd do
  let env ← getEnv
  let mut tally : Std.HashMap String Nat := {}
  let mut total := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    for (i, _) in (optBinders ci.type).1 do
      total := total + 1
      let v := verdictP env nm i
      tally := tally.insert v ((tally.getD v 0) + 1)
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let got := s!"total={total} {body}"
  if got != expectedOptTallyP then
    throwError "the PEELED optional-context census moved.\nexpected: {
      expectedOptTallyP}\ngot:      {got}"
  -- and `content_dispatch_routed`'s six are where item 225 left them
  let rows := (optBinders (env.find? ``content_dispatch_routed).get!.type).1
  let gotC := rows.toList.map (fun (i, bn) =>
    s!"{verdictP env ``content_dispatch_routed i} content_dispatch_routed#{i} ({bn})")
  if gotC != expectedContentDispatch then
    throwError "the peel moved content_dispatch_routed's contexts.\nexpected:\n{
      String.intercalate "\n" expectedContentDispatch}\ngot:\n{
      String.intercalate "\n" gotC}"

/-! ## §4  Item 225's §5, landed

Every one of the nine reaches a mechanism.  Two of them reach a LIBRARY
elimination — `accum_block_on_closeThenBlock`'s `Or.casesOn` — which is exactly
what "no terminal inside `L4YAML`" denied, and `indicator_open_map`'s lands at
`rootMapRoute_or_refused`, the same refutation site item 225 found for
`content_dispatch_routed`'s `h_ref`.

The count is asserted beside the rows, because an empty shortlist that is not
also counted passes vacuously. -/

def expectedNineResolved : List String :=
  [ "accum_block_on_pendingBlock#28 (h_seqF_old) => ELIM@L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock#28>Or.casesOn#3",
    "accum_block_on_pendingBlockContent#33 (h_seqF_old) => ELIM@L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock#28>Or.casesOn#3",
    "accum_block_on_pendingContent#31 (h_seqF168) => RETURN@L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent#31",
    "accum_content_on_pendingMapValue_indented#14 (h_ncol_old) => FIELD@L4YAML.Proofs.StreamAccum.PendingNode.pendingProps#19",
    "colon_open_map#24 (h_cov_in) => FIELD@And.intro#2",
    "flowKeyRoute_of_root#19 (h_tail143) => RETURN@L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root#19",
    "indicator_open_map#26 (h_ref_land) => ELIM@L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused.match_1_1#4, ELIM@L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused.match_1_1#4",
    "question_open_map#23 (h_cov_in) => FIELD@And.intro#2",
    "question_open_map#24 (h_cov_nil) => FIELD@And.intro#2" ]

/-- `h_ref`'s terminals, with the pipe peeled: the `SPLIT@Eq.ndrec#9` row item
    225 published was the over-applied transport, not a site. -/
def expectedRefTerminalsP : List String :=
  [ "ELIM@L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused.match_1_1#4",
    "ELIM@L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused#7>L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused.match_1_1#4" ]

run_cmd do
  let env ← getEnv
  let nine : List (Name × Nat) :=
    [ (``accum_block_on_pendingBlock, 28), (``accum_block_on_pendingBlockContent, 33),
      (``accum_block_on_pendingContent, 31), (``accum_content_on_pendingMapValue_indented, 14),
      (``colon_open_map, 24), (``flowKeyRoute_of_root, 19), (``indicator_open_map, 26),
      (``question_open_map, 23), (``question_open_map, 24) ]
  if nine.length != expectedCoreTerminal.length then
    throwError "item 225's shortlist is no longer nine rows"
  let got := nine.map (fun (c, i) =>
    let bn := (optBinders (env.find? c).get!.type).1.findSome?
      (fun q => if q.1 == i then some q.2 else none) |>.getD `_
    let ts := (chaseP env 30 c i).toList.mergeSort (fun a b => a < b)
    s!"{c.getString!}#{i} ({bn}) => {String.intercalate ", " ts}")
  if got != expectedNineResolved then
    throwError "the resolved nine moved.\nexpected:\n{
      String.intercalate "\n" expectedNineResolved}\ngot:\n{
      String.intercalate "\n" got}"
  -- …and re-derived, the shortlist is EMPTY, asserted as a count.
  let mut core : Nat := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    for (i, _) in (optBinders ci.type).1 do
      if verdictP env nm i != "RELAY" then continue
      if (chaseP env 30 nm i).toList.all (fun t => !isLibTerminal t) then
        core := core + 1
  if core != 0 then
    throwError "the peeled core-terminal shortlist is not empty: {core}"
  let refT := (chaseP env 30 ``content_dispatch_routed 24).toList.mergeSort
    (fun a b => a < b)
  if refT != expectedRefTerminalsP then
    throwError "h_ref's peeled terminals moved.\nexpected:\n{
      String.intercalate "\n" expectedRefTerminalsP}\ngot:\n{
      String.intercalate "\n" refT}"

/-! ## §5  Item 225's §7, decided

`Or.elim` reads and `Or.imp_left` re-states, and with the pipe peeled the
census says so: the read RELAYS into a constant that eliminates, the
re-statement RETURNS the premise weakened.  Item 225's debt row is retired. -/

def expectedDistinguished : String :=
  "reads_by_elim#3=RELAY restates_by_imp#3=RETURN"

run_cmd do
  let env ← getEnv
  let got := s!"reads_by_elim#3={verdictP env ``reads_by_elim 3} restates_by_imp#3={
    verdictP env ``restates_by_imp 3}"
  if got != expectedDistinguished then
    throwError "§5's two relays are no longer distinguished.\nexpected: {
      expectedDistinguished}\ngot:      {got}"
  if expectedDistinguished == expectedIndistinguishable then
    throwError "the peeled and blind walks agree on §7's exhibits, so one of \
      the two pins has been edited to match the other"

/-! ## §6  The dead-parameter fixpoint

ALIVE is the least fixpoint, so DEAD never calls a read premise dead.  The
`inTy`/`usedLaterInType` clause is the one a census does not need and a DROP
does: item 225's walk peels the telescope before it walks, so it cannot see a
binder named in a LATER binder's type. -/

structure Node where
  c : Name
  i : Nat
deriving BEq, Hashable, Inhabited

def nkey (n : Node) : String := s!"{n.c}#{n.i}"

/-- Does binder `i` of `c` occur in a later binder's type or in the conclusion? -/
def usedLaterInType (env : Environment) (c : Name) (i : Nat) : Bool :=
  match env.find? c with
  | none => true
  | some ci => Id.run do
      let mut t := ci.type
      for _ in [0:i+1] do
        match t with
        | .forallE _ _ b _ => t := b
        | _ => return true
      return t.hasLooseBVar 0

/-- `(base-ALIVE, relay targets)`.  No accessible value means ALIVE: the
    fixpoint calls a binder alive when it cannot call it dead. -/
def baseOf (env : Environment) (n : Node) : Bool × Array Node :=
  match binderUsesP env n.c n.i with
  | none => (true, #[])
  | some us =>
      if usedLaterInType env n.c n.i then (true, #[]) else
      Id.run do
        let mut b := false
        let mut tg : Array Node := #[]
        for u in us do
          match u with
          | .relay g j => tg := tg.push ⟨g, j⟩
          | _ => b := true
        return (b, tg)

abbrev Graph := Std.HashMap String (Node × Bool × Array Node)

partial def build (env : Environment) : List Node → Graph → Graph
  | [], g => g
  | n :: rest, g =>
      if g.contains (nkey n) then build env rest g
      else
        let (b, tg) := baseOf env n
        build env (tg.toList ++ rest) (g.insert (nkey n) (n, b, tg))

/-- The least fixpoint, by reverse-edge propagation. -/
def aliveSet (g : Graph) : Std.HashSet String := Id.run do
  let mut rev : Std.HashMap String (Array String) := {}
  let mut alive : Std.HashSet String := {}
  let mut queue : Array String := #[]
  for (k, (_, b, tg)) in g do
    for t in tg do
      let tk := nkey t
      rev := rev.insert tk ((rev.getD tk #[]).push k)
    if b then
      alive := alive.insert k
      queue := queue.push k
  let mut idx := 0
  while h : idx < queue.size do
    let k := queue[idx]
    idx := idx + 1
    for s in rev.getD k #[] do
      if !alive.contains s then
        alive := alive.insert s
        queue := queue.push s
  return alive

/-- Ten dead binders in the whole explored closure, and every one is `UNUSED`.
    Nine are `StreamAccum`'s own — item 225's `expectedUnused`, which the peel
    does not move — and the tenth is one module over. -/
def expectedDead : List String :=
  [ "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline#10 (_h_res) [class marker]",
    "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#10 (_h_src) [class marker]",
    "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#11 (_h_indent) [class marker]",
    "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#12 (_h_park) [class marker]",
    "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#11 (_h_src) [class marker]",
    "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#12 (_h_indent) [class marker]",
    "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#13 (_h_ne) [class marker]",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close#10 (_) [conclusion binder]",
    "L4YAML.Proofs.StreamAccum.question_open_map#15 (_h_noflow_disp) [family uniformity]",
    "L4YAML.Proofs.StructureCoupling.scanTagDirective_corr#2 (_hcorr) [family uniformity]" ]

/-- Why each dead binder is there.  The reading is a JUDGEMENT read off the
    source and it is written down so a later reader can disagree with it; what
    is measured is the set, not the reasons. -/
def deadReason : String → String
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline#10"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#10"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#11"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack#12"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#11"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#12"
  | "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol#13" => "class marker"
  | "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close#10" => "conclusion binder"
  | _ => "family uniformity"

def expectedDeadTally : String := "dead=10 UNUSED=10 RELAY=0"

run_cmd do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``colon_fires_implicit_key
  let mut q : Array Node := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm == modIdx then
      for (i, _) in ← propBinders nm do q := q.push ⟨nm, i⟩
    if (`L4YAML).isPrefixOf nm && !(`L4YAML.Tests).isPrefixOf nm
        && !isMechanism env nm then
      for (i, _) in (optBinders ci.type).1 do q := q.push ⟨nm, i⟩
  let g := build env q.toList {}
  let alive := aliveSet g
  let mut dead : Array String := #[]
  let mut tally : Std.HashMap String Nat := {}
  for (k, (n, _, _)) in g do
    if alive.contains k then continue
    let v := verdictP env n.c n.i
    tally := tally.insert v ((tally.getD v 0) + 1)
    let bn := match env.find? n.c with
      | none => `_
      | some ci => Id.run do
          let mut t := ci.type
          for _ in [0:n.i] do
            match t with | .forallE _ _ b _ => t := b | _ => return `_
          match t with | .forallE nm _ _ _ => return nm | _ => return `_
    dead := dead.push s!"{n.c} ({shownName bn}) [{deadReason k}]"
  let got := (dead.qsort (· < ·)).toList
  -- the rows carry the constant and the binder name; re-attach the index
  let gotIdx := ((g.toList.filterMap (fun (k, (n, _, _)) =>
      if alive.contains k then none else some (k, n))).mergeSort
      (fun a b => a.1 < b.1)).map (fun (k, n) =>
    let bn := match env.find? n.c with
      | none => `_
      | some ci => Id.run do
          let mut t := ci.type
          for _ in [0:n.i] do
            match t with | .forallE _ _ b _ => t := b | _ => return `_
          match t with | .forallE nm _ _ _ => return nm | _ => return `_
    s!"{k} ({shownName bn}) [{deadReason k}]")
  if gotIdx != expectedDead then
    throwError "the DEAD set moved.\nexpected ({expectedDead.length}):\n{
      String.intercalate "\n" expectedDead}\ngot ({gotIdx.length}):\n{
      String.intercalate "\n" gotIdx}"
  if got.length != expectedDead.length then
    throwError "dead row count disagreement"
  let body := String.intercalate " " ((tally.toList.mergeSort
    (fun a b => a.1 < b.1)).map (fun (k, v) => s!"{k}={v}"))
  let gotT := s!"dead={gotIdx.length} {body} RELAY={tally.getD "RELAY" 0}"
  if gotT != expectedDeadTally then
    throwError "the DEAD tally moved.\nexpected: {expectedDeadTally}\ngot:      {gotT}"

/-! ## §7  Why the optional lane is free, in one line

`A ∨ True` is unconditionally inhabited, so a premise of that shape constrains
nothing and a consumer takes it for free.  This is item 225's §6 corollary —
*a premise whose type is unconditionally inhabited has no reader at any price*
— applied to the population item 225 had just censused and did not apply it to.

`isOptTy` is the selector items 212–225 have used throughout, so the 163 rows
those censuses count are definitionally the rows these lemmas discharge — and
item 227 measures what that selector MISSES, which is two rows and one
definition. -/

/-- The whole of the optional-context lane, as a proposition. -/
lemma opt_is_unconditional (A : Prop) : A ∨ True := Or.inr trivial

/-- …so a consumer that takes one proves its goal without it. -/
lemma opt_premise_buys_nothing {A P : Prop} (k : A ∨ True → P) : P :=
  k (opt_is_unconditional A)

/-- …and the lemma that takes one is the lemma that does not, which is what
    the substitution probe verifies at the level of the PROOF rather than the
    statement. -/
lemma opt_premise_is_no_premise {A P : Prop} : (A ∨ True → P) ↔ P :=
  ⟨fun k => opt_premise_buys_nothing k, fun p _ => p⟩

/-- The population the three lemmas above cover: every binder items 212–225
    census is selected BY the shape they discharge, and there are ~~163 of
    them~~ **163 that `isOptTy` can SEE**.

    **Corrected at item 227.**  `isOptTy` is a test on the syntax, so a
    `∨ True` behind a definition is invisible to it, and `ResumeKeyCtx` is one:
    two further binders carry an optional context this selector does not
    report, so **the optional population is 165**.  The pin below is right —
    it pins what `isOptTy` finds, and it still passes unedited — and so is
    every measurement items 212–226 took over the 163, because each of them
    measured the 163.  What was wrong is this sentence, which called the 163
    the population.  `Tests.Guards.NarrowingWorthCensus` §6 runs the two
    selectors against each other and gates the difference.

    The pin is the count, because a selector that matched nothing would make
    the sentence above true and empty. -/
def expectedOptPopulation : String := "total=163 optTy=163 ctorFields=34"

run_cmd do
  let env ← getEnv
  let mut total := 0
  let mut optTy := 0
  let mut ctorFields := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    let mut t := ci.type
    let mut j := 0
    for (i, _) in (optBinders ci.type).1 do
      total := total + 1
      if isCtor env nm then ctorFields := ctorFields + 1
      while j < i do
        t := match t with | .forallE _ _ b _ => b | x => x
        j := j + 1
      if (match t with | .forallE _ a _ _ => isOptTy a | _ => false) then
        optTy := optTy + 1
  let got := s!"total={total} optTy={optTy} ctorFields={ctorFields}"
  if got != expectedOptPopulation then
    throwError "the optional population moved.\nexpected: {
      expectedOptPopulation}\ngot:      {got}"

end Tests.Guards.PremiseNecessityCensus
