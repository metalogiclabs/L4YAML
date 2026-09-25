/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.PuntCoverInputs

/-!
# What the one refused relay would add to the trees, once the root's literal and the content sibling's relay are made (DOCS items 255–256)

Item 255 priced the four payments item 254 found in hand — the root `-`'s
floor-zero cover and three relays — by rewriting item 253's rows in the row
array and re-resolving its trees with the same resolver: one leaf turns paid,
the root's, and the relays turn none.  Item 256 made two of the four: the
root's literal (`IndentStackCover.covered_nil_of_ntop`, threaded `h_mono`)
and the content sibling's relay of `h_closeF_old`.  The compact fill's relay
of `h_valF` cannot be made — that closure awaits a block node read at the
park's position, and the compact fill's node is a compact sequence on the
slot's own line — and the mapping value content's relay of `h_frames99`
forwards a cover floored at the props park's entry index, item 148's
vacuity, and is refused.  This module keeps the refused relay as the one
payment in hand and reads what it would add.

**§1** runs item 253's walk unchanged, checked against its pinned rows and
its pinned tree lines — the trees as they stand with the two payments made.
**§2** rewrites the refused relay's row in the row array — the module throws
unless the row is found once and is a bare punt — and re-resolves the
content and entry trees under two scenarios, without it and with it.  **§3**
reads the floors a relay could carry: every `Exists.intro` in an L4YAML
theorem whose motive is a `Floor` with its cover, the witness against the
index — the index itself, another closed term, or a variable carried from a
source — and the applications of the floor transports per lemma.  **§4**
reads the root payment's price as paid: the root lemma and its caller both
bind the stack's monotonicity.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropDependents (sorted)
open Tests.Guards.RouteShapes
open Tests.Guards.StreamCompositions
open Tests.Guards.OpenEntryRoute
open Tests.Guards.CloseLandingWidth
open Tests.Guards.CloseSplitFrames
open Tests.Guards.CloseStackCover
open Tests.Guards.PuntCoverInputs
set_option autoImplicit false

namespace Tests.Guards.PaidLeafDelta

/-! ## §0 The payment in hand, as the class its row would carry -/

/-- A payment in hand: the row it rewrites and the
    classification the rewritten row carries.  `kind` says whether the class
    pays from nothing (`literal`) or forwards a source (`relay`). -/
structure Payment where
  key : String
  lem : Name
  occ : Nat
  target : String
  kind : String
  src : String
  cls : CloseStackCover.Cls
  deriving Inhabited

/-- The one payment in hand that is not made: the mapping value content's
    relay of `h_frames99` into the props park's entry face, refused by item 255
    because the cover it forwards stands at that face's own index. -/
def payments : List Payment :=
  [{ key := "R4", lem := ``accum_content_on_pendingMapValue_indented, occ := 1, target := "ctor:pendingProps.h_closeFE",
     kind := "relay", src := "h_frames99",
     cls := .alt "match" #[.paid (.step (.relay "param:accum_content_on_pendingMapValue_indented.h_frames99")), .punt] }]

def scenarios : List (String × List String) :=
  [("none", []), ("R4", ["R4"])]

def roots : List (String × String) :=
  [("content", "param:accum_block_on_pendingBlockContent.h_closeF_old"), ("entry", "ctor:pendingBlock.h_closeF")]

def isTarget (p : Payment) (r : CloseStackCover.Row) : Bool :=
  r.lem == p.lem && r.occ == p.occ && r.target == p.target

/-- Rewrite one row; the row must exist once and be a bare punt. -/
def rewrite (rows : Array CloseStackCover.Row) (p : Payment) : MetaM (Array CloseStackCover.Row) := do
  let hits := rows.filter (isTarget p)
  unless hits.size == 1 do throwError "{p.key}: {hits.size} rows match {short p.lem} #{p.occ} {p.target}"
  unless hits[0]!.cls.isPunt do throwError "{p.key}: the row is not a punt: {hits[0]!.cls.render}"
  return rows.map fun r => if isTarget p r then { r with cls := p.cls } else r

/-! ## §1 The leaf census of a resolved tree -/

structure Leaves where
  positions : Nat := 0
  rows : Nat := 0
  paid : Nat := 0
  punt : Nat := 0
  coverPunt : Nat := 0
  opens : Nat := 0
  lemmaPaid : Nat := 0
  other : Nat := 0
  origins : Nat := 0
  deriving Inhabited, Repr

def cnt (xs : Array String) (l : String) : Nat := (xs.filter (· == l)).size

def leavesOf (rows : Array CloseStackCover.Row) (t : Tree) : Leaves :=
  let rs := (t.visited.toList.map fun p => (rowsAt rows p).size).foldl (· + ·) 0
  -- a paid ORIGIN is a row reached whose class pays from nothing (a `lit`
  -- with no source) — a relay of it is not a second origin
  let origins := (t.visited.toList.map fun p => ((rowsAt rows p).filter fun r => r.cls.leaves.contains "paid").size).foldl (· + ·) 0
  { positions := t.visited.size, rows := rs, paid := cnt t.leaves "paid", punt := cnt t.leaves "punt",
    coverPunt := cnt t.leaves "cover-punt", opens := t.opens.size, lemmaPaid := cnt t.leaves "paid:lemma",
    other := (t.leaves.filter fun l => l.startsWith "other(" || l == "depth").size, origins := origins }

def Leaves.render (l : Leaves) : String :=
  s!"positions={l.positions} rows={l.rows} paid={l.paid} punt={l.punt} cover-punt={l.coverPunt} open={l.opens} origins={l.origins}"

def sdelta (a b : Nat) : String := if b ≥ a then s!"+{b - a}" else s!"-{a - b}"

def Leaves.delta (base l : Leaves) : String :=
  s!"Δ(paid={sdelta base.paid l.paid} punt={sdelta base.punt l.punt} cover-punt={sdelta base.coverPunt l.coverPunt} open={sdelta base.opens l.opens} positions={sdelta base.positions l.positions})"

def sameSet (a b : Std.HashSet String) : Bool :=
  a.size == b.size && a.toList.all b.contains

/-! ## §2 The floors: literals and transports -/

def floorN' : Name := ``L4YAML.Proofs.IndentStackCover.Floor

def transports : List Name :=
  [``L4YAML.Proofs.IndentStackCover.Floor.mono_index, ``L4YAML.Proofs.IndentStackCover.Floor.cons,
   ``L4YAML.Proofs.IndentStackCover.Floor.pop_to, ``L4YAML.Proofs.IndentStackCover.Floor.le_of_mem,
   ``L4YAML.Proofs.IndentStackCover.Covered.pop_to, ``L4YAML.Proofs.IndentStackCover.Covered.raise_floor,
   ``L4YAML.Proofs.IndentStackCover.Covered.dedup_head, ``L4YAML.Proofs.IndentStackCover.Covered.cons]

structure FloorLit where
  lem : Name
  witness : String
  idx : String
  ks : String
  cls : String
  deriving Inhabited

structure FS where
  lits : Array FloorLit := #[]
  apps : Std.HashMap (Name × Name) Nat := {}
  memo : Std.HashMap Expr Bool := {}
  nodes : Nat := 0

/-- Does `e` mention a floor or a transport?  Memoized, so the scan below
    walks only the paths that lead to one. -/
partial def hasFloor (st : IO.Ref FS) (e : Expr) : MetaM Bool := do
  if let some b := (← st.get).memo[e]? then return b
  let r ← match e with
    | .const n _ => pure (n == floorN' || transports.contains n)
    | .app f a => pure ((← hasFloor st f) || (← hasFloor st a))
    | .lam _ t b _ | .forallE _ t b _ => pure ((← hasFloor st t) || (← hasFloor st b))
    | .letE _ t v b _ => pure ((← hasFloor st t) || (← hasFloor st v) || (← hasFloor st b))
    | .mdata _ b => hasFloor st b
    | .proj _ _ b => hasFloor st b
    | _ => pure false
  st.modify fun s => { s with memo := s.memo.insert e r }
  return r

/-- The witness class of a `Floor` literal: the index itself, a variable, or
    another closed term. -/
def witnessClass (w n : Expr) : String :=
  if w.consumeMData == n.consumeMData then "own"
  else match w.consumeMData with
    | .bvar _ => "var"
    | _ => "lit"

partial def scanFloors (st : IO.Ref FS) (lem : Name) (stk : Stack) (e : Expr) : MetaM Unit := do
  unless ← hasFloor st e do return
  st.modify fun s => { s with nodes := s.nodes + 1 }
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const n _ := f then
      if transports.contains n then
        st.modify fun s => { s with apps := s.apps.insert (n, lem) (s.apps.getD (n, lem) 0 + 1) }
      if n == ``Exists.intro && args.size ≥ 4 then
        let p := args[1]!.consumeMData
        if let .lam _ _ body _ := p then
          let inst := (body.instantiate1 args[2]!).consumeMData
          if inst.isAppOfArity ``And 2 then
            let fl := inst.appFn!.appArg!.consumeMData
            if fl.isAppOfArity floorN' 3 then
              let fa := fl.getAppArgs
              let lit : FloorLit := { lem := lem, witness := pp stk fa[0]!, idx := pp stk fa[1]!, ks := pp stk fa[2]!, cls := witnessClass fa[0]! fa[1]! }
              st.modify fun s => { s with lits := s.lits.push lit }
    scanFloors st lem stk f
    for a in args do scanFloors st lem stk a
  | .lam n t b _ | .forallE n t b _ =>
    scanFloors st lem (stk.push { name := n, ty := t, prov := none }) b
  | .letE n t v b _ =>
    scanFloors st lem stk v
    scanFloors st lem (stk.push { name := n, ty := t, prov := none }) b
  | .mdata _ b => scanFloors st lem stk b
  | .proj _ _ b => scanFloors st lem stk b
  | _ => pure ()

/-! ## §3 The pins -/

def expectedTrees255 : List String :=
  ["none content: positions=16 rows=47 paid=2 punt=19 cover-punt=2 open=2 origins=2 Δ(paid=+0 punt=+0 cover-punt=+0 open=+0 positions=+0)",
   "none entry: positions=16 rows=47 paid=2 punt=19 cover-punt=2 open=2 origins=2 Δ(paid=+0 punt=+0 cover-punt=+0 open=+0 positions=+0)",
   "none merged=true",
   "R4 content: positions=18 rows=54 paid=2 punt=20 cover-punt=2 open=2 origins=2 Δ(paid=+0 punt=+1 cover-punt=+0 open=+0 positions=+2)",
   "R4 entry: positions=18 rows=54 paid=2 punt=20 cover-punt=2 open=2 origins=2 Δ(paid=+0 punt=+1 cover-punt=+0 open=+0 positions=+2)",
   "R4 merged=true"]
def expectedPayments : List String :=
  ["R4 relay accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_closeFE idx=n + 1 src=h_frames99@2:Floor(n,ks) tgt=bound(ks<ne) Floor(ne,ks) eq(n=ne + 1) := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_frames99))}|punt]"]
def expectedFloorLits : List String :=
  ["accum_block_on_closeThenBlock lo=lo idx=k ks=nv :: ksv var ×1",
   "accum_block_on_noPending lo=0 idx=k ks=[] lit ×1",
   "accum_block_on_pendingBlockContent lo=lo idx=k ks=ks var ×1",
   "accum_content_on_pendingBlock_indented lo=lo idx=n ks=ks var ×5",
   "accum_content_on_pendingMapValue_indented lo=lo idx=n + 1 ks=ks var ×5",
   "accum_content_on_pendingMapValue_indented lo=lo idx=n ks=ks var ×1",
   "accum_content_on_pendingMapValue_indented lo=lo idx=n ks=n :: ks var ×4",
   "accum_content_pending lo=lo idx=k ks=k :: ks var ×10",
   "accum_content_pending lo=lo idx=k ks=ks var ×3",
   "accum_content_pending lo=lo idx=m ks=ks var ×14",
   "accum_content_pending lo=lo idx=n ks=ks var ×1",
   "accum_content_pending lo=lo idx=ne ks=ks var ×3",
   "colon_fires_implicit_key lo=lo idx=k ks=k :: ks var ×2",
   "colon_fires_props_key lo=lo idx=k ks=k :: ks var ×2",
   "colon_open_map lo=k idx=k ks=k :: [] own ×5",
   "colon_open_map_implicit lo=lo idx=k + 1 ks=k :: ks var ×2",
   "colon_open_map_implicit lo=lo idx=k ks=k :: ks var ×2",
   "colon_open_map_props lo=lo idx=k + 1 ks=k :: ks var ×2",
   "colon_open_map_props lo=lo idx=k ks=k :: ks var ×2",
   "content_dispatch_routed lo=lo idx=k ks=k :: ks var ×2",
   "content_dispatch_routed lo=lo idx=k ks=k :: ksv var ×2",
   "dedent_cover_of_floor lo=lo idx=w ks=w :: ks' var ×1",
   "entryKeyPack_of_dispatch lo=lo idx=w ks=w :: ks var ×2",
   "entryPropsKeyPack_of_dispatch lo=lo idx=w ks=w :: ks var ×2",
   "question_open_map lo=k + 1 idx=k + 1 ks=[] own ×2",
   "question_open_map lo=k idx=k ks=k :: [] own ×5"]
def expectedTransports : List String :=
  ["Floor.mono_index: 9 in 5 [accum_block_on_closeThenBlock=1, colon_open_map_implicit=2, colon_open_map_props=2, entryKeyPack_of_dispatch=2, entryPropsKeyPack_of_dispatch=2]",
   "Floor.cons: 4 in 2 [entryKeyPack_of_dispatch=2, entryPropsKeyPack_of_dispatch=2]",
   "Floor.pop_to: 1 in 1 [dedent_cover_of_floor=1]",
   "Floor.le_of_mem: 0 in 0 []",
   "Covered.pop_to: 1 in 1 [dedent_cover_of_floor=1]",
   "Covered.raise_floor: 0 in 0 []",
   "Covered.dedup_head: 2 in 2 [colon_open_map_implicit=1, colon_open_map_props=1]",
   "Covered.cons: 4 in 2 [entryKeyPack_of_dispatch=2, entryPropsKeyPack_of_dispatch=2]"]
def expectedLine : String :=
  "rows=169 payments=1 literal=0 relay=1 scenarios=2 baseContent=16/2/19/2/2 allContent=18/2/20/2/2 baseEntry=16/2/19/2/2 allEntry=18/2/20/2/2 turnedPaidContent=0 turnedPaidEntry=0 originsBaseContent=2 originsAllContent=2 originsBaseEntry=2 originsAllEntry=2 puntContent=+1 puntEntry=+1 coverPuntContent=+0 coverPuntEntry=+0 mergedBase=true mergedAll=true floorLits=82 own=12 lit=1 var=69 ownLemmas=2 scanned=32 monoIndex=9 monoIndexLemmas=5 floorCons=4 floorConsLemmas=2 floorPopTo=1 floorPopToLemmas=1 leOfMem=0 coveredPopTo=1 coveredPopToLemmas=1 raiseFloor=0 dedupHead=2 dedupHeadLemmas=2 coveredCons=4 rootMonoCaller=1 rootMonoSite=1 rootNtop=1 nodes=95157 floorNodes=24315"

/-! ## §4 The reading -/

set_option maxHeartbeats 20000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- item 253's candidates, rebuilt the same way
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let mut cd : Cand := {}
  for c in iv.ctors do
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut i := 0
    let mut fields : Array (Nat × Name × List CloseStackCover.Step) := #[]
    let mut names : Array Name := #[]
    while true do
      match ty with
      | .forallE n t b _ =>
        if i ≥ cv.numParams then
          names := names.push n
          if let some p := coverPath t then fields := fields.push (i, n, p)
        ty := b; i := i + 1
      | _ => break
    cd := { cd with ctorFieldNames := cd.ctorFieldNames.insert c names, ctorNames := cd.ctorNames.push c, consts := cd.consts.insert c }
    if !fields.isEmpty then cd := { cd with ctorFields := cd.ctorFields.insert c fields }
  cd := { cd with consts := cd.consts.insert ``PendingNode.casesOn }
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML || n == ``PendingNode then continue
    match ci with
    | .inductInfo ivv =>
      if ivv.ctors.any (fun c => match env.find? c with | some cc => hasCov cc.type | none => false) then
        cd := { cd with coverTypes := cd.coverTypes.insert n }
    | .defnInfo dv =>
      if (piConcl dv.type).isSort && hasCov dv.value then
        cd := { cd with coverTypes := cd.coverTypes.insert n }
    | _ => pure ()
  let coverMod := `L4YAML.Proofs.Scanner.IndentStackCover
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML then continue
    match ci with
    | .thmInfo _ =>
      thms := thms.push n
      let mut ty := ci.type
      let mut i := 0
      let mut ps : Array (Nat × Name × List CloseStackCover.Step) := #[]
      let mut names : Array (Name × Bool) := #[]
      while true do
        match ty with
        | .forallE pn t b _ =>
          let cp := if hasCov t then coverPath t else none
          names := names.push (pn, cp.isSome)
          if let some p := cp then ps := ps.push (i, pn, p)
          ty := b; i := i + 1
        | _ => break
      cd := { cd with paramNames := cd.paramNames.insert n names }
      let inCoverMod := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod
      let transport := (piConcl ci.type).isAppOf coveredN || (inCoverMod && hasCov (piConcl ci.type))
      if !ps.isEmpty && !transport then
        cd := { cd with lemParams := cd.lemParams.insert n ps, consts := cd.consts.insert n }
    | _ => pure ()
  for (l, p) in [(``indicator_open_map, `h_stream_land), (``colon_open_map_explicit, `h_stream_mid),
      (``block_dispatch_deferred_stamp_offcol, `h_stream), (``block_dispatch_deferred_stamp_nopack, `h_stream)] do
    let some ci := env.find? l | throwError "{l}: missing"
    let some idx := ci.type.getForallBinderNames.toArray.findIdx? (· == p) | throwError "{l}.{p}: missing"
    cd := { cd with funnels := cd.funnels.insert l (idx, p), consts := cd.consts.insert l }
  cd := { cd with parks := ({} : Std.HashSet Name).insert ``accum_block_on_pendingBlock |>.insert ``accum_block_on_pendingBlockContent }
  -- item 253's walk, unchanged
  let st ← IO.mkRef ({} : CloseStackCover.S)
  let thmsS := sorted thms
  for n in thmsS do
    if (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod then continue
    walkTheorem st cd n
  let w ← st.get
  let rowLines := w.rows.map fun r => s!"  {short r.lem} #{r.occ} {r.target} := {r.cls.render}"
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "item 253's rows (CloseStackCover.expectedRows)" rowLines Tests.Guards.CloseStackCover.expectedRows
  -- §1 the baseline trees, item 253's four, checked against its pins
  let mut rets : Std.HashMap String (Array String) := {}
  for (l, ps) in cd.lemParams.toList do
    rets := rets.insert s!"ret:{short l}" (ps.map fun (_, pn, _) => posLabel "param" l pn)
  let roots253 := [("content", "param:accum_block_on_pendingBlockContent.h_closeF_old"), ("entry", "ctor:pendingBlock.h_closeF"),
    ("valF", "param:accum_block_on_closeThenBlock.h_valF"), ("mapValue", "ctor:pendingMapValue.h_closeF")]
  let mut base253 : Array String := #[]
  for (nm, root) in roots253 do
    let t := resolve rets w.rows root 0 {}
    let rs := (t.visited.toList.map fun p => (rowsAt w.rows p).size).foldl (· + ·) 0
    base253 := base253.push s!"  {nm}: positions={t.visited.size} rows={rs} leaves[{census t.leaves}] open={t.opens.size}"
  check "item 253's trees (CloseStackCover.expectedTrees)" base253 Tests.Guards.CloseStackCover.expectedTrees
  -- §2 the scenarios
  let payOf (k : String) : MetaM Payment := do
    let some p := payments.find? (·.key == k) | throwError "no payment {k}"
    return p
  let mut treeLines : Array String := #[]
  let mut treeText : Array String := #[]
  let mut baseL : Std.HashMap String Leaves := {}
  let mut allL : Std.HashMap String Leaves := {}
  let mut mergedBase := false
  let mut mergedAll := false
  for (sc, ks) in scenarios do
    let mut rows := w.rows
    for k in ks do rows ← rewrite rows (← payOf k)
    let mut visited : Array (Std.HashSet String) := #[]
    for (nm, root) in roots do
      let t := resolve rets rows root 0 {}
      let l := leavesOf rows t
      if sc == "none" then baseL := baseL.insert nm l
      if sc == "R4" then allL := allL.insert nm l
      let d := match baseL[nm]? with | some b => " " ++ b.delta l | none => ""
      treeLines := treeLines.push s!"  {sc} {nm}: {l.render}{d}"
      visited := visited.push t.visited
      if sc == "R4" || sc == "none" then
        treeText := treeText ++ #[s!"--- {sc} {nm}"] ++ t.lines
    let merged := sameSet visited[0]! visited[1]!
    treeLines := treeLines.push s!"  {sc} merged={merged}"
    if sc == "none" then mergedBase := merged
    if sc == "R4" then mergedAll := merged
  -- the payments, with the relays' source shapes (item 254's reading of the
  -- row's own stack) and the target's index and field shape
  let idxOf (r : CloseStackCover.Row) : MetaM String := do
    let ctorShort := ((r.target.drop 5).toString.splitOn ".")[0]!
    let some c := cd.ctorNames.find? (fun c => short c == ctorShort) | throwError "{r.target}: no constructor"
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut i := 0
    let mut idx : Option Nat := none
    while idx.isNone do
      match ty with
      | .forallE _ t b _ =>
        if i ≥ cv.numParams && t.consumeMData.isConstOf ``Nat then idx := some i
        ty := b; i := i + 1
      | _ => break
    let some j := idx | throwError "{c}: no Nat field"
    unless j < r.args.size do throwError "{c}: {r.args.size} args"
    return ppc r.st r.args[j]!
  let mut payLines : Array String := #[]
  for p in payments do
    let some r := w.rows.find? (isTarget p) | throwError "{p.key}: no row"
    let idx ← idxOf r
    let ins := inputsAt r.st
    let srcShape := if p.src.isEmpty then "—" else
      match ins.cover.find? (fun c => c.startsWith (p.src ++ "@")) with
      | some c => c
      | none => s!"{p.src}:NOT IN HAND"
    let tgtField := (p.target.drop 5).toString
    let tgtShape := match Tests.Guards.PuntCoverInputs.expectedShapes.find? (·.startsWith (tgtField ++ " ")) with
      | some s => (s.drop (tgtField.length + 1)).toString
      | none => "—"
    payLines := payLines.push s!"  {p.key} {p.kind} {short p.lem} #{p.occ} {p.target} idx={idx} src={srcShape} tgt={tgtShape} := {p.cls.render}"
  -- §3 the floors
  let fs ← IO.mkRef ({} : FS)
  let mut scanned : Nat := 0
  for n in thmsS do
    if (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod then continue
    let some (.thmInfo ti) := env.find? n | continue
    let v := ti.value
    let mentions := v.foldConsts false fun c acc => acc || c == floorN' || transports.contains c
    unless mentions do continue
    scanned := scanned + 1
    scanFloors fs n #[] v
  let f ← fs.get
  -- the literals, aggregated: one row per (lemma, witness, index, list, class) with its count
  let litKeys := distinctS (f.lits.map fun l => s!"{short l.lem} lo={l.witness} idx={l.idx} ks={l.ks} {l.cls}")
  let litLines := (litKeys.qsort (· < ·)).map fun k =>
    s!"  {k} ×{(f.lits.filter fun l => s!"{short l.lem} lo={l.witness} idx={l.idx} ks={l.ks} {l.cls}" == k).size}"
  let short2 (n : Name) : String := String.intercalate "." ((n.components.drop (n.components.length - 2)).map (·.toString))
  let mut trLines : Array String := #[]
  for t in transports do
    let per := (f.apps.toList.filter fun ((n, _), _) => n == t).map fun ((_, l), k) => (short l, k)
    let per := per.toArray.qsort (fun a b => a.1 < b.1)
    let total := per.foldl (fun a (_, k) => a + k) 0
    trLines := trLines.push s!"  {short2 t}: {total} in {per.size} [{String.intercalate ", " (per.toList.map fun (l, k) => s!"{l}={k}")}]"
  -- §4 the root's price
  let bindersOf (n : Name) : MetaM (Array Name) := do
    let some ci := env.find? n | throwError "{n}: missing"
    return ci.type.getForallBinderNames.toArray
  let rootMonoCaller := (← bindersOf ``accum_block_pending).contains `h_mono
  let rootMonoSite := (← bindersOf ``accum_block_on_noPending).contains `h_mono
  let rootNtop := (← bindersOf ``accum_block_on_noPending).contains `h_ntop
  -- the counts
  let b := fun nm => baseL.getD nm {}
  let a := fun nm => allL.getD nm {}
  let bC := b "content"; let aC := a "content"; let bE := b "entry"; let aE := a "entry"
  let trTotal (t : Name) := (f.apps.toList.filter fun ((n, _), _) => n == t).foldl (fun acc (_, k) => acc + k) 0
  let trLems (t : Name) := (f.apps.toList.filter fun ((n, _), _) => n == t).length
  let litC (c : String) := (f.lits.filter (·.cls == c)).size
  let litLems := (distinctS (f.lits.filter (·.cls == "own") |>.map fun l => short l.lem)).size
  let got := s!"rows={w.rows.size} payments={payments.length} literal={(payments.filter (·.kind == "literal")).length} relay={(payments.filter (·.kind == "relay")).length} scenarios={scenarios.length} \
baseContent={bC.positions}/{bC.paid}/{bC.punt}/{bC.coverPunt}/{bC.opens} allContent={aC.positions}/{aC.paid}/{aC.punt}/{aC.coverPunt}/{aC.opens} \
baseEntry={bE.positions}/{bE.paid}/{bE.punt}/{bE.coverPunt}/{bE.opens} allEntry={aE.positions}/{aE.paid}/{aE.punt}/{aE.coverPunt}/{aE.opens} \
turnedPaidContent={aC.paid - bC.paid} turnedPaidEntry={aE.paid - bE.paid} originsBaseContent={bC.origins} originsAllContent={aC.origins} originsBaseEntry={bE.origins} originsAllEntry={aE.origins} \
puntContent={sdelta bC.punt aC.punt} puntEntry={sdelta bE.punt aE.punt} coverPuntContent={sdelta bC.coverPunt aC.coverPunt} coverPuntEntry={sdelta bE.coverPunt aE.coverPunt} \
mergedBase={mergedBase} mergedAll={mergedAll} \
floorLits={f.lits.size} own={litC "own"} lit={litC "lit"} var={litC "var"} ownLemmas={litLems} scanned={scanned} \
monoIndex={trTotal transports[0]!} monoIndexLemmas={trLems transports[0]!} floorCons={trTotal transports[1]!} floorConsLemmas={trLems transports[1]!} \
floorPopTo={trTotal transports[2]!} floorPopToLemmas={trLems transports[2]!} leOfMem={trTotal transports[3]!} coveredPopTo={trTotal transports[4]!} coveredPopToLemmas={trLems transports[4]!} \
raiseFloor={trTotal transports[5]!} dedupHead={trTotal transports[6]!} dedupHeadLemmas={trLems transports[6]!} coveredCons={trTotal transports[7]!} \
rootMonoCaller={if rootMonoCaller then 1 else 0} rootMonoSite={if rootMonoSite then 1 else 0} rootNtop={if rootNtop then 1 else 0} nodes={w.nodes} floorNodes={f.nodes}"
  logInfo s!"PaidLeafDelta {got}"
  logInfo s!"trees:\n{String.intercalate "\n" treeLines.toList}"
  logInfo s!"payments:\n{String.intercalate "\n" payLines.toList}"
  logInfo s!"floorlits:\n{String.intercalate "\n" litLines.toList}"
  logInfo s!"transports:\n{String.intercalate "\n" trLines.toList}"
  logInfo s!"treetext:\n{String.intercalate "\n" treeText.toList}"
  unless payments.length == 1 do throwError "one payment expected"
  check "expectedTrees255" treeLines expectedTrees255
  check "expectedPayments" payLines expectedPayments
  check "expectedFloorLits" litLines expectedFloorLits
  check "expectedTransports" trLines expectedTransports
  unless got == expectedLine do
    throwError "PaidLeafDelta moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.PaidLeafDelta
