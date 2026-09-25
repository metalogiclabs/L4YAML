/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.CloseStackCover

/-!
# How many of the eleven producers that punt a park's resume stack hold a cover's inputs, and at what floor (DOCS item 254)

Item 253 found the entry park's field punted at six of its seven producers,
the mapping value park's at two of six and the props park's entry face at
three of six — eleven producers that hand a park a stack with no cover.  The
one literal payment in the library, `indicator_cover_at_col`, takes the
stack's monotonicity and base, the landing's floor and the dispatch; where
those stand in hand a punt is a choice, and where they do not it is a debt
with a producer's name on it.  This module reads, at each of the eleven,
what stands in hand against that signature, and which floor a payment there
could name.

**§1** re-finds the eleven off item 253's walk: `Row` carries the binder
stack and the constructor's arguments at every constructor row, so the same
walk, checked against item 253's pinned rows, hands this module the context
of each punt.  **§2** reads the stack by shape — a hypothesis counts only
where its conclusion IS the shape; one that mentions the shape inside an
option is listed apart and credited nothing.  **§3** is the verdict: the
inputs present or the names missing, and the floor each site could name —
its own index where a top bound or a landed arm stands, zero where the top
bound is negative, a relay's floor where a cover-carrying hypothesis stands,
with that cover's `Floor` index and list printed so a floor at the park's own
index is never read as a floor below it.  **§4** reads the four field types
themselves: the frames bound, the cover's list and the `Floor`'s index — the
shape that decides whether an own-index payment is statable at all.  **§5**
(item 258) reads each site's top bound against its index: the floor
`covered_nil_of_top_le` gives from it, whether the bound stands strictly
below the index — syntactically, or by a binder in scope — and beside it the
state the bound is about, whether `Mono` in hand is about that state, and
whether the site is landed or inline, since a bound on an earlier state
crosses preprocessing's unwind at a landed site.

**Item 256 pays two of the eleven**: the root `-` its own field, from the
seed's empty stack at floor 0 (`IndentStackCover.covered_nil_of_ntop`), and
the content park's sibling by relaying `h_closeF_old` at the unchanged index.
The compact fill's relay of `h_valF` is refuted there — that closure awaits
a block node read at the park's position, and the compact fill's node is a
compact sequence on the slot's own line — and **item 257 pays the compact
fill a third way**: a literal from the slot's own top bound
(`IndentStackCover.covered_nil_of_top_le`), floored at `nv + 1` below the
fill's index `nv + 1 + m`, because the top bound that site holds is the
SLOT's and not the park's — the reading item 254's own-index verdict did not
take.  **Item 258 pays two more the same way**, from the entry park's own top
bound `h_top_old`: its inline compact re-park (`- - a`, floor `n + 1` below
the index `n + 1 + m`) and its nested landing (`-⏎  - a`, floor `n + 1` below
the index `k` by the arm's `n < k`) — the landed site's bound is the OLD
park's, and it transports because preprocessing's unwind only pops.  Six
punts remain, and the reading below is theirs: three hold no top bound and
three hold one at their own index, so none holds the shape these payments
spend.
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
set_option autoImplicit false

namespace Tests.Guards.PuntCoverInputs

/-- The three positions item 253 found punted, and the content park's field
    beside them for the shape reading. -/
def targets : List String :=
  ["ctor:pendingBlock.h_closeF", "ctor:pendingMapValue.h_closeF", "ctor:pendingProps.h_closeFE"]

def shapeTargets : List (Name × Name) :=
  [(``PendingNode.pendingBlock, `h_closeF), (``PendingNode.pendingBlockContent, `h_closeF),
   (``PendingNode.pendingMapValue, `h_closeF), (``PendingNode.pendingProps, `h_closeFE)]

/-! ## §0 Printing: characters, casts and the directive update -/

partial def ppc (st : Stack) (e : Expr) : String :=
  let e := e.consumeMData
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const n _ =>
    if n == ``Char.ofNat && args.size == 1 then
      match args[0]!.consumeMData with
      | .lit (.natVal v) => s!"'{Char.ofNat v}'"
      | _ => pp st e
    else if (n == ``Nat.cast || n == ``NatCast.natCast || n == ``Int.ofNat || n == ``Int.cast || n == ``IntCast.intCast) && args.size ≥ 1 then
      ppc st args[args.size - 1]!
    else if n == ``ite && args.size ≥ 5 then s!"{ppc st args[4]!}*"
    else if n == ``ScannerState.currentIndent && args.size == 1 then s!"{ppc st args[0]!}.currentIndent"
    else if n == ``ScannerState.col && args.size == 1 then s!"{ppc st args[0]!}.col"
    else if n == ``SurfPos.col && args.size == 1 then s!"{ppc st args[0]!}.col"
    else pp st e
  | _ => pp st e

/-- A relation, `Not` stripped, as (symbol, left, right). -/
def rel (t : Expr) : Option (String × Expr × Expr) :=
  let t := t.consumeMData
  let (neg, t) := if t.isAppOfArity ``Not 1 then (true, (t.getArg! 0).consumeMData) else (false, t)
  if t.isAppOfArity ``Eq 3 then some (if neg then "≠" else "=", t.getArg! 1, t.getArg! 2)
  else if t.isAppOfArity ``Ne 3 then some ("≠", t.getArg! 1, t.getArg! 2)
  else if t.isAppOfArity ``LE.le 4 then some ("≤", t.getArg! 2, t.getArg! 3)
  else if t.isAppOfArity ``LT.lt 4 then some ("<", t.getArg! 2, t.getArg! 3)
  else if t.isAppOfArity ``GE.ge 4 then some ("≤", t.getArg! 3, t.getArg! 2)
  else if t.isAppOfArity ``GT.gt 4 then some ("<", t.getArg! 3, t.getArg! 2)
  else none

/-- The structure an operand projects `proj` off: the operand is the
    projection, or a cast or a query one level over it. -/
def projOf (o : Expr) (proj : Name) : Option Expr :=
  let o := o.consumeMData
  if o.isAppOf proj then o.getAppArgs.back?
  else o.getAppArgs.findSome? fun a =>
    let a := a.consumeMData
    if a.isAppOf proj then a.getAppArgs.back? else none

def isZeroE (e : Expr) : Bool :=
  let e := e.consumeMData
  match e with
  | .lit (.natVal 0) => true
  | _ => e.isAppOfArity ``OfNat.ofNat 3 && (match (e.getArg! 1).consumeMData with | .lit (.natVal 0) => true | _ => false)

def isBoolLit (e : Expr) (b : Bool) : Bool :=
  e.consumeMData.isConstOf (if b then ``Bool.true else ``Bool.false)

/-- The state and character a preprocess equation's right side names:
    `.ok (some (s', c))`. -/
def digPrep (st : Stack) (rhs : Expr) : String :=
  let rhs := rhs.consumeMData
  let inner := if rhs.isAppOf ``Except.ok then (rhs.getAppArgs.back?.getD rhs).consumeMData else rhs
  let inner := if inner.isAppOf ``Option.some then (inner.getAppArgs.back?.getD inner).consumeMData else inner
  if inner.isAppOfArity ``Prod.mk 4 then s!"{ppc st (inner.getArg! 2)},{ppc st (inner.getArg! 3)}" else ppc st inner

/-- The first sub-term `p` accepts, descending through binders (whose names
    are pushed so widths print by name) and applications. -/
partial def findFirst (st : Stack) (t : Expr) (p : Stack → Expr → Option String) : Option String :=
  let t := t.consumeMData
  match p st t with
  | some s => some s
  | none =>
    match t with
    | .forallE n ty b _ => findFirst (st.push { name := n, ty := ty, prov := none }) b p
    | .lam n ty b _ => findFirst (st.push { name := n, ty := ty, prov := none }) b p
    | .app .. => t.getAppArgs.findSome? fun a => findFirst st a p
    | _ => none

def floorShape (st : Stack) (t : Expr) : Option String :=
  findFirst st t fun st t =>
    if t.isAppOfArity floorN 3 then some s!"Floor({ppc st (t.getArg! 1)},{ppc st (t.getArg! 2)})" else none

/-- `∀ k' ∈ ks, k' < n`: the frames bound, as its relation, list and bound. -/
def boundShape (st : Stack) (t : Expr) : Option String :=
  findFirst st t fun st t =>
    match t with
    | .forallE n ty b _ =>
      let ty := ty.consumeMData
      if ty.isAppOfArity ``Membership.mem 5 then
        let st' := st.push { name := n, ty := ty, prov := none }
        match rel b with
        | some (r, _, rhs) => some s!"bound({ppc st (ty.getArg! 3)}{r}{ppc st' rhs})"
        | none => none
      else none
    | _ => none

def eqShape (st : Stack) (t : Expr) : Option String :=
  findFirst st t fun st t =>
    match rel t with
    | some ("=", l, r) => if (l.consumeMData.isBVar || r.consumeMData.isBVar) && !(hasHead t ``ScannerState.col) && !(hasHead t ``SurfPos.col) then some s!"eq({ppc st l}={ppc st r})" else none
    | _ => none

/-! ## §1 The inputs in hand -/

structure Inputs where
  mono : Array String := #[]
  monoOpt : Array String := #[]
  base : Array String := #[]
  baseOpt : Array String := #[]
  prep : Array String := #[]
  dispB : Array String := #[]
  dispC : Array String := #[]
  hc : Array String := #[]
  chr : Array String := #[]
  corr : Array String := #[]
  noflow : Array String := #[]
  save : Array String := #[]
  fl : Array String := #[]
  top : Array String := #[]
  larm : Array String := #[]
  floor : Array String := #[]
  nic : Array String := #[]
  armed : Array String := #[]
  col0 : Array String := #[]
  ids : Array String := #[]
  cover : Array String := #[]
  coverFn : Array String := #[]
  -- item 258: the top bounds as (name, state, relation, bound), and every
  -- relation in hand as (name, relation, left, right), for the reading of a
  -- bound against the site's index
  tops : Array (String × String × String × String) := #[]
  rels : Array (String × String × String × String) := #[]
  deriving Inhabited

def monoN : Name := ``L4YAML.Proofs.IndentStackMono.Mono
def baseN : Name := ``L4YAML.Proofs.IndentStackBase.SentinelBase
def ifloorN : Name := ``L4YAML.Proofs.PreprocessIndentStable.IndentFloor

/-- A hypothesis whose conclusion is a conjunction has each conjunct in hand;
    one under an implication is kept whole (its premises apply to all of it).
    Only a NAMED hypothesis is split: the inaccessible binders a destructuring
    leaves behind (`right✝`) hold the same conjuncts its named pieces do. -/
partial def conjuncts (nm : String) (t : Expr) : Array (String × Expr) :=
  let t := t.consumeMData
  if t.isForall then #[(nm, t)]
  else if t.isAppOfArity ``And 2 then conjuncts (nm ++ ".1") (t.getArg! 0) ++ conjuncts (nm ++ ".2") (t.getArg! 1)
  else #[(nm, t)]

/-- The conclusion of a Pi type with its premises PUSHED, so the conclusion's
    indices resolve. -/
partial def piConclSt (st : Stack) (t : Expr) : Stack × Expr :=
  match t.consumeMData with
  | .forallE n ty b _ => piConclSt (st.push { name := n, ty := ty, prov := none }) b
  | t => (st, t)

def inputsAt (stAll : Stack) : Inputs := Id.run do
  let mut r : Inputs := {}
  for i in [0:stAll.size] do
    let b := stAll[i]!
    -- a binder's type was elaborated under the binders BEFORE it: its de
    -- Bruijn indices resolve against the prefix, not the whole stack
    let st0 := stAll.extract 0 i
    let t := b.ty
    let (st, c) := piConclSt st0 t
    let isPi := t.consumeMData.isForall
    if hasCov t then
      if isPi then r := { r with coverFn := r.coverFn.push (bname b.name) }
      else r := { r with cover := r.cover.push s!"{bname b.name}@{(depthTo t (·.isAppOf coveredN)).getD 0}:{(floorShape st0 t).getD "—"}" }
      continue
    if isPi && hasHead c ``ScannerState.simpleKeyAllowed && hasHead c ``ScannerState.currentIndent then
      r := { r with larm := r.larm.push (bname b.name) }; continue
    if c.isAppOfArity ``Or 2 && (c.getArg! 0).consumeMData.isAppOfArity ``Eq 3 && ((c.getArg! 0).consumeMData.getArg! 0).consumeMData.isConstOf ``Char then
      let l := (c.getArg! 0).consumeMData
      let rr := (c.getArg! 1).consumeMData
      let rhs2 := if rr.isAppOfArity ``Eq 3 then ppc st (rr.getArg! 2) else "?"
      r := { r with hc := r.hc.push s!"{(if isPi then "→" else "")}{bname b.name}:{ppc st (l.getArg! 2)}|{rhs2}" }; continue
    let parts := if b.name.hasMacroScopes then #[(bname b.name, t)] else conjuncts (bname b.name) t
    -- mentioned inside an option or a disjunction, and not in hand directly
    if hasHead t monoN && !(parts.any fun (_, pt) => (piConcl pt).isAppOf monoN) then r := { r with monoOpt := r.monoOpt.push (bname b.name) }
    if hasHead t baseN && !(parts.any fun (_, pt) => (piConcl pt).isAppOf baseN) then r := { r with baseOpt := r.baseOpt.push (bname b.name) }
    for (pn, pt) in parts do
      -- a fact under an implication is marked: in hand once its premise is
      let nm := (if pt.isForall then "→" else "") ++ pn
      let (st, c) := piConclSt st0 pt
      if c.isAppOf monoN then r := { r with mono := r.mono.push s!"{nm}:{ppc st (c.getArg! 0)}" }; continue
      if c.isAppOf baseN then r := { r with base := r.base.push s!"{nm}:{ppc st (c.getArg! 0)}" }; continue
      if c.isAppOf ifloorN then r := { r with floor := r.floor.push s!"{nm}:{ppc st (c.getArg! 0)}@{ppc st (c.getArg! 1)}" }; continue
      if c.isAppOf ``L4YAML.Proofs.CouplingBridge.ScannerSurfCorr then r := { r with corr := r.corr.push s!"{nm}:{ppc st (c.getArg! 0)}" }; continue
      -- item 258: a relation in hand directly (not under a premise), as printed
      if let some (sym, l, rr) := rel c then
        if !pt.isForall then r := { r with rels := r.rels.push (nm, sym, ppc st l, ppc st rr) }
      match rel c with
      | some ("=", l, rhs) =>
        if c.isAppOfArity ``Eq 3 && (c.getArg! 0).consumeMData.isConstOf ``Char then
          r := { r with chr := r.chr.push s!"{nm}:{ppc st l}={ppc st rhs}" }
        else if l.isAppOf ``scanNextToken_preprocess then
          r := { r with prep := r.prep.push s!"{nm}:{ppc st (l.getArg! 0)}→{digPrep st rhs}" }
        else if l.isAppOf ``scanNextToken_dispatchBlockIndicators && l.getAppNumArgs ≥ 2 then
          r := { r with dispB := r.dispB.push s!"{nm}:{ppc st (l.getArg! 1)}" }
        else if l.isAppOf ``scanNextToken_dispatchContent && l.getAppNumArgs ≥ 2 then
          r := { r with dispC := r.dispC.push s!"{nm}:{ppc st (l.getArg! 1)}" }
        else if (projOf l ``ScannerState.inFlow).isSome && isBoolLit rhs false then
          r := { r with noflow := r.noflow.push nm }
        else if let some s := projOf l ``ScannerState.needIndentCheck then
          if isBoolLit rhs false then r := { r with nic := r.nic.push s!"{nm}:{ppc st s}" }
          else if isBoolLit rhs true then r := { r with armed := r.armed.push s!"{nm}:{ppc st s}" }
        else if (projOf l ``ScannerState.indents).isSome || (projOf rhs ``ScannerState.indents).isSome then
          r := { r with ids := r.ids.push nm }
        else if hasHead l ``ScannerState.simpleKey && hasHead rhs ``ScannerState.col then
          r := { r with save := r.save.push nm }
        else if ((projOf l ``SurfPos.col).isSome && isZeroE rhs) || ((projOf rhs ``SurfPos.col).isSome && isZeroE l) then
          r := { r with col0 := r.col0.push s!"{nm}:{ppc st l}={ppc st rhs}" }
      | some ("≠", l, rhs) =>
        if ((projOf l ``SurfPos.col).isSome && isZeroE rhs) || ((projOf rhs ``SurfPos.col).isSome && isZeroE l) then
          r := { r with col0 := r.col0.push s!"{nm}:{ppc st l}≠{ppc st rhs}" }
      | some (sym, l, rhs) =>
        if let some s := projOf l ``ScannerState.currentIndent then
          if hasHead rhs ``ScannerState.col then r := { r with fl := r.fl.push s!"{nm}:{ppc st s}{sym}col" }
          else r := { r with top := r.top.push s!"{nm}:{ppc st s}{sym}{ppc st rhs}",
                               tops := r.tops.push (nm, ppc st s, sym, ppc st rhs) }
        else if isZeroE l && (projOf rhs ``SurfPos.col).isSome then
          r := { r with col0 := r.col0.push s!"{nm}:0{sym}{ppc st rhs}" }
      | none => pure ()
  return r

def Inputs.render (r : Inputs) : String :=
  let f (k : String) (xs : Array String) := s!"{k}={xs.size}{if xs.isEmpty then "" else "(" ++ String.intercalate "," xs.toList ++ ")"}"
  String.intercalate " " [f "mono" r.mono, f "monoOpt" r.monoOpt, f "base" r.base, f "baseOpt" r.baseOpt, f "prep" r.prep,
    f "dispB" r.dispB, f "dispC" r.dispC, f "hc" r.hc, f "chr" r.chr, f "corr" r.corr, f "noflow" r.noflow, f "save" r.save,
    f "fl" r.fl, f "top" r.top, f "larm" r.larm, f "floor" r.floor, f "nic" r.nic, f "armed" r.armed,
    f "col0" r.col0, f "ids" r.ids, f "cover" r.cover, f "coverFn" r.coverFn]

/-- The verdict: the payment's inputs present or the names missing, and the
    floors a payment here could name. -/
def verdict (r : Inputs) (idx : String) : String := Id.run do
  -- a floor SOURCE bounds the top from above: the dispatch state's floor,
  -- the landed arm, a top bound, or the armed flag `park_col0_floor` spends;
  -- `IndentFloor` bounds it from below and is no source
  let floorSrc := !r.fl.isEmpty || !r.larm.isEmpty || !r.top.isEmpty || !r.armed.isEmpty
  let mut missing : Array String := #[]
  if r.mono.isEmpty then missing := missing.push "mono"
  if r.base.isEmpty then missing := missing.push "base"
  if r.prep.isEmpty then missing := missing.push "prep"
  if r.dispB.isEmpty && r.dispC.isEmpty then missing := missing.push "disp"
  if !floorSrc then missing := missing.push "floorSrc"
  let inputs := if missing.isEmpty then (if r.dispB.isEmpty then "full(dispC)" else "full") else s!"missing({String.intercalate "," missing.toList})"
  let mut lo : Array String := #[]
  if floorSrc then lo := lo.push s!"own={idx}"
  if r.top.any (fun (s : String) => (s.splitOn "<0").length > 1) then lo := lo.push "empty=0"
  for cv in r.cover do
    if let some i := (cv.splitOn ":Floor(")[1]? then lo := lo.push s!"relay={(cv.splitOn "@")[0]!}:Floor({i}"
  return s!"inputs={inputs} lo=[{String.intercalate ";" lo.toList}]{if idx == "0" then " idx0" else ""}"

/-! ## §5 The bound against the index (item 258) -/

/-- The summands of a left-nested `+`, printed: `n + 1 + m` reads `[n, 1, m]`. -/
partial def summands (st : Stack) (e : Expr) : List String :=
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then summands st (e.getArg! 4) ++ [ppc st (e.getArg! 5)]
  else [ppc st e]

def isPosLit (s : String) : Bool := match s.toNat? with | some v => decide (v > 0) | none => false

/-- One top bound `state sym rhs` against the index: the floor
    `IndentStackCover.covered_nil_of_top_le` gives from it (`rhs + 1` under a
    weak bound, `rhs` under a strict one), and where the bound stands —
    `below` the index when the index is the bound plus a positive literal or
    a binder in scope says `rhs < idx`, `at` it when the two print the same
    or a binder equates them, `above` when a binder puts the index at or
    under the bound, `undecided` otherwise.  A strict bound is one below a
    weak one, so it is below the index already where the two print the same. -/
def boundVs (idx : String) (idxSum : List String) (rels : Array (String × String × String × String))
    (sym rhs : String) : String × String × String := Id.run do
  let floor := if sym == "≤" then s!"{rhs} + 1" else rhs
  if idx == rhs then return (floor, if sym == "<" then "below" else "at", "syn")
  if idxSum.head? == some rhs && (idxSum.drop 1).any isPosLit then return (floor, "below", "syn")
  if let some (h, s, l, r) := rels.find? (fun (_, s, l, r) => (s == "<" || (sym == "<" && s == "≤")) && l == rhs && r == idx) then
    return (floor, "below", s!"by {h}:{l}{s}{r}")
  if let some (h, _, l, r) := rels.find? (fun (_, s, l, r) => s == "=" && ((l == rhs && r == idx) || (l == idx && r == rhs))) then
    return (floor, "at", s!"by {h}:{l}={r}")
  if let some (h, s, l, r) := rels.find? (fun (_, s, l, r) => (s == "<" || s == "≤") && l == idx && r == rhs) then
    return (floor, "above", s!"by {h}:{l}{s}{r}")
  return (floor, "undecided", "—")

/-- Where the site stands on its line: `landed` when the landed arm's
    hypothesis or a `.col = 0` fact stands, `inline` when a `.col ≠ 0` or
    `0 < .col` fact does — the datum a bound on an EARLIER state is read
    beside, because at a landed site preprocessing's unwind ran between that
    state and the constructor's. -/
def whereOf (r : Inputs) : String :=
  let landed := !r.larm.isEmpty || r.col0.any fun s => (s.splitOn "=0").length > 1 && (s.splitOn "≠0").length == 1
  let inline := r.col0.any fun s => (s.splitOn "≠0").length > 1 || (s.splitOn ":0<").length > 1
  if landed && inline then "both" else if landed then "landed" else if inline then "inline" else "—"

structure BoundRead where
  line : String
  cls : Array String
  hows : Array String
  own : Array Bool
  payable : Bool
  site : String
  deriving Inhabited

/-- The site's bounds read against its index, and the verdict: `payable`
    when a bound is below the index, `Mono` in hand is about the bound's
    state, and that state is the constructor's or the preprocess and the
    dispatch transport it — item 257's payment term verbatim. -/
def readBounds (r : Inputs) (idx : String) (idxSum : List String) (ctorState : String) : BoundRead := Id.run do
  let monoStates := r.mono.map fun s => ((s.splitOn ":").getLast?).getD ""
  let transport := !r.prep.isEmpty && (!r.dispB.isEmpty || !r.dispC.isEmpty)
  let mut parts : Array String := #[]
  let mut cls : Array String := #[]
  let mut hows : Array String := #[]
  let mut owns : Array Bool := #[]
  let mut payable := false
  for (nm, state, sym, rhs) in r.tops do
    let (floor, c, how) := boundVs idx idxSum r.rels sym rhs
    let own := state == ctorState
    let monoOk := monoStates.contains state
    if c == "below" && monoOk && (own || transport) then payable := true
    let monoS := if monoOk then "yes" else if r.mono.isEmpty then "—" else "no"
    parts := parts.push s!"{nm}:{state}{sym}{rhs} floor={floor} {c}({how}) {if own then "own" else "old"} mono={monoS}"
    cls := cls.push c; hows := hows.push how; owns := owns.push own
  let w := whereOf r
  let verdict :=
    if r.tops.isEmpty then "no-bound"
    else if payable then "payable"
    else if cls.contains "below" then "below-unpayable"
    else if cls.contains "at" then "at-index"
    else if cls.contains "above" then "above-index"
    else "undecided"
  return { line := s!"idx={idx} ctor={ctorState} where={w} bounds=[{String.intercalate "; " parts.toList}] ⊢ {verdict}",
           cls, hows, own := owns, payable, site := w }

/-! ## §2 The pins -/

def expectedSites : List String :=
  ["accum_block_on_pendingBlock #1 ctor:pendingBlock.h_closeF idx=k mono=1(h_mono:sc) monoOpt=0 base=1(h_base:sc) baseOpt=0 prep=1(h_preprocess:sc→s_prep,c) dispB=1(h_dispatch:c) dispC=0 hc=0 chr=1(hc:c='-') corr=5(hcorr_prep:s_prep,hcorr_result:s',h_corr:sc,hcorr_sc:s_prep,hcorr_dash2:s') noflow=1(h_noflow) save=0 fl=0 top=1(h_top_old:sc≤n) larm=1(h_larm) floor=0 nic=1(h_nic_old:sc) armed=0 col0=2(h_landed.2.1:sp_mid.col=0,hcol_mid:sp_mid.col=0) ids=0 cover=0 coverFn=0 ⊢ inputs=full lo=[own=k]",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_closeFE idx=n + 1 mono=1(h_mono:sc) monoOpt=0 base=1(h_base:sc) baseOpt=0 prep=1(h_preprocess:sc→s_prep,c) dispB=0 dispC=1(h_dispatch:c) hc=0 chr=0 corr=3(hcorr_prep:s_prep,hcorr_result:s',h_corr:sc) noflow=1(h_flow_disp) save=1(h_sk_s) fl=0 top=0 larm=0 floor=1(h_floor_old:sc@n + 1) nic=2(h_nic_mv:sc,h_nic_s:s') armed=0 col0=1(h_col0_old:0<sp_scan.col) ids=0 cover=4(h_closeF99@2:Floor(n,n :: ks),h_frames99@2:Floor(n,ks),h_closeFV108@2:Floor(n + 1,ks),h_framesV108@2:Floor(n + 1,ks)) coverFn=1(h_cov_step) ⊢ inputs=missing(floorSrc) lo=[relay=h_closeF99:Floor(n,n :: ks);relay=h_frames99:Floor(n,ks);relay=h_closeFV108:Floor(n + 1,ks);relay=h_framesV108:Floor(n + 1,ks)]",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_closeF idx=nv mono=0 monoOpt=0 base=0 baseOpt=0 prep=0 dispB=1(h_dispatch:':') dispC=0 hc=0 chr=0 corr=3(hcorr_prep:s_prep,hcorr_result:s',hcorr_colon:s') noflow=1(h_noflow_disp) save=0 fl=0 top=1(h_top_in:s'≤nv) larm=0 floor=1(h_floor_in:s'@nv + 1) nic=2(h_nic_disp:s_prep*,hpf.1:s') armed=0 col0=1(hcol_mid:sp_mid.col=0) ids=0 cover=0 coverFn=0 ⊢ inputs=missing(mono,base,prep) lo=[own=nv]",
   "compact_open_map #1 ctor:pendingMapValue.h_closeF idx=n + 1 + m mono=0 monoOpt=0 base=0 baseOpt=0 prep=1(h_preprocess:sc→s_prep,c) dispB=1(h_dispatch:c) dispC=0 hc=1(hc:':'|'?') chr=0 corr=2(hcorr_prep:s_prep,hcorr_result:s') noflow=1(h_noflow_disp) save=0 fl=0 top=1(h_top_in:s'≤n + 1 + m) larm=0 floor=1(h_floor:s'@n + 1 + m + 1) nic=2(h_nic_disp:s_prep*,hpk.1:s') armed=0 col0=0 ids=0 cover=0 coverFn=0 ⊢ inputs=missing(mono,base) lo=[own=n + 1 + m]",
   "content_dispatch_routed #1 ctor:pendingProps.h_closeFE idx=0 mono=0 monoOpt=0 base=0 baseOpt=0 prep=0 dispB=0 dispC=1(h_dispatch:c) hc=1(hprops:'&'|'!') chr=1(h:c='&') corr=3(hcorr_prep:s_prep,hcorr_result:s',hc:s') noflow=1(h_flow_disp) save=0 fl=0 top=0 larm=0 floor=0 nic=3(h_nic_prep:s_prep,h_nic_ad:s_prep*,h_nic_s:s') armed=0 col0=0 ids=0 cover=0 coverFn=1(h_cov_lift) ⊢ inputs=missing(mono,base,prep,floorSrc) lo=[] idx0",
   "content_dispatch_routed #2 ctor:pendingProps.h_closeFE idx=0 mono=0 monoOpt=0 base=0 baseOpt=0 prep=0 dispB=0 dispC=1(h_dispatch:c) hc=1(hprops:'&'|'!') chr=1(h:c='!') corr=3(hcorr_prep:s_prep,hcorr_result:s',hc:s') noflow=1(h_flow_disp) save=0 fl=0 top=0 larm=0 floor=0 nic=3(h_nic_prep:s_prep,h_nic_ad:s_prep*,h_nic_s:s') armed=0 col0=0 ids=0 cover=0 coverFn=1(h_cov_lift) ⊢ inputs=missing(mono,base,prep,floorSrc) lo=[] idx0"]
def expectedShapes : List String :=
  ["pendingBlock.h_closeF bound(ks<n) Floor(n,ks) eq(—)",
   "pendingBlockContent.h_closeF bound(ks<n) Floor(n,ks) eq(—)",
   "pendingMapValue.h_closeF bound(ks<n) Floor(n,n :: ks) eq(—)",
   "pendingProps.h_closeFE bound(ks<ne) Floor(ne,ks) eq(n=ne + 1)"]
def expectedBounds : List String :=
  ["accum_block_on_pendingBlock #1 idx=k ctor=s' where=landed bounds=[h_top_old:sc≤n floor=n + 1 at(by hkn:k=n) old mono=yes] ⊢ at-index",
   "accum_content_on_pendingMapValue_indented #1 idx=n + 1 ctor=s' where=inline bounds=[] ⊢ no-bound",
   "colon_open_map_explicit #1 idx=nv ctor=s' where=landed bounds=[h_top_in:s'≤nv floor=nv + 1 at(syn) own mono=—] ⊢ at-index",
   "compact_open_map #1 idx=n + 1 + m ctor=s' where=— bounds=[h_top_in:s'≤n + 1 + m floor=n + 1 + m + 1 at(syn) own mono=—] ⊢ at-index",
   "content_dispatch_routed #1 idx=0 ctor=s' where=— bounds=[] ⊢ no-bound",
   "content_dispatch_routed #2 idx=0 ctor=s' where=— bounds=[] ⊢ no-bound"]
def expectedLine : String :=
  "sites=6 pb=1 pmv=2 props=3 idx0=2 mono=2 monoOpt=0 base=2 baseOpt=0 prep=3 dispB=3 dispC=3 hc=3 chr=3 dash=1 corr=6 noflow=6 save=1 fl=0 top=3 larm=1 floor=3 nic=6 armed=0 col0=3 ids=0 coverSites=1 coverBinders=4 coverFnSites=3 full=1 fullB=1 missMono=4 missBase=4 missPrep=3 missFloorSrc=3 own=3 empty=0 relay=1 relayEntries=4 bounds=3 below=0 belowSyn=0 belowArm=0 at=3 atSyn=2 atArm=1 undecided=0 bOwn=2 bOld=1 landedBelow=0 inlineBelow=0 payable=0 rows=169 nodes=95157"

/-! ## §3 The reading -/

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
  for n in sorted thms do
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
  -- §1 the eleven
  let punts := w.rows.filter fun r => r.kind == "ctor" && targets.contains r.target && r.cls.isPunt
  let idxOf (r : CloseStackCover.Row) : MetaM (String × List String) := do
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
    return (ppc r.st r.args[j]!, summands r.st r.args[j]!)
  let mut siteLines : Array String := #[]
  let mut sites : Array (CloseStackCover.Row × String × Inputs) := #[]
  -- §5: the bound against the index, read beside each site
  let mut boundLines : Array String := #[]
  let mut reads : Array BoundRead := #[]
  for r in punts do
    let (idx, idxSum) ← idxOf r
    let ins := inputsAt r.st
    unless r.args.size > 0 do throwError "{r.target}: no constructor arguments"
    let br := readBounds ins idx idxSum (ppc r.st r.args[0]!)
    sites := sites.push (r, idx, ins)
    reads := reads.push br
    siteLines := siteLines.push s!"  {short r.lem} #{r.occ} {r.target} idx={idx} {ins.render} ⊢ {verdict ins idx}"
    boundLines := boundLines.push s!"  {short r.lem} #{r.occ} {br.line}"
  -- §4 the shapes
  let mut shapeLines : Array String := #[]
  for (c, f) in shapeTargets do
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut stk : Stack := #[]
    let mut found : Option String := none
    while found.isNone do
      match ty with
      | .forallE n t b _ =>
        if n == f then
          found := some s!"  {short c}.{f} {(boundShape stk t).getD "bound(—)"} {(floorShape stk t).getD "Floor(—)"} {(eqShape stk t).getD "eq(—)"}"
        stk := stk.push { name := n, ty := t, prov := none }
        ty := b
      | _ => break
    let some l := found | throwError "{c}.{f}: no such field"
    shapeLines := shapeLines.push l
  -- the counts
  let n (p : Inputs → Array String) := (sites.filter fun (_, _, i) => !(p i).isEmpty).size
  let vs := sites.map fun (_, idx, i) => verdict i idx
  let cnt (s : String) := (vs.filter fun v => (v.splitOn s).length > 1).size
  let byT (t : String) := (sites.filter fun (r, _, _) => r.target == t).size
  -- §5's counts: sites, each counted once
  let nb (p : BoundRead → Bool) := (reads.filter p).size
  let has (c : String) (b : BoundRead) := b.cls.contains c
  let hasHow (c : String) (syn : Bool) (b : BoundRead) := (b.cls.zip b.hows).any fun (x, h) => x == c && (h == "syn") == syn
  let boundCounts := s!"bounds={nb (!·.cls.isEmpty)} below={nb (has "below")} belowSyn={nb (hasHow "below" true)} belowArm={nb (hasHow "below" false)} \
at={nb (has "at")} atSyn={nb (hasHow "at" true)} atArm={nb (hasHow "at" false)} undecided={nb fun b => !b.cls.isEmpty && !has "below" b && !has "at" b && !has "above" b} \
bOwn={nb (·.own.contains true)} bOld={nb (·.own.contains false)} landedBelow={nb fun b => has "below" b && b.site == "landed"} inlineBelow={nb fun b => has "below" b && b.site == "inline"} payable={nb (·.payable)}"
  let got := s!"sites={sites.size} pb={byT "ctor:pendingBlock.h_closeF"} pmv={byT "ctor:pendingMapValue.h_closeF"} props={byT "ctor:pendingProps.h_closeFE"} \
idx0={cnt " idx0"} mono={n (·.mono)} monoOpt={n (·.monoOpt)} base={n (·.base)} baseOpt={n (·.baseOpt)} prep={n (·.prep)} dispB={n (·.dispB)} dispC={n (·.dispC)} \
hc={n (·.hc)} chr={n (·.chr)} dash={(sites.filter fun (_, _, i) => i.chr.any fun x => (x.splitOn "='-'").length > 1).size} corr={n (·.corr)} noflow={n (·.noflow)} save={n (·.save)} fl={n (·.fl)} top={n (·.top)} larm={n (·.larm)} floor={n (·.floor)} nic={n (·.nic)} armed={n (·.armed)} \
col0={n (·.col0)} ids={n (·.ids)} coverSites={n (·.cover)} coverBinders={sites.foldl (fun a (_, _, i) => a + i.cover.size) 0} coverFnSites={n (·.coverFn)} \
full={cnt "inputs=full"} fullB={cnt "inputs=full "} missMono={cnt "missing(mono"} missBase={(vs.filter fun v => (v.splitOn "base").length > 1).size} missPrep={(vs.filter fun v => (v.splitOn "prep").length > 1).size} missFloorSrc={cnt "floorSrc"} \
own={cnt "own="} empty={cnt "empty=0"} relay={cnt "relay="} relayEntries={vs.foldl (fun a v => a + ((v.splitOn "relay=").length - 1)) 0} \
{boundCounts} rows={w.rows.size} nodes={w.nodes}"
  logInfo s!"PuntCoverInputs {got}"
  logInfo s!"sites:\n{String.intercalate "\n" siteLines.toList}"
  logInfo s!"shapes:\n{String.intercalate "\n" shapeLines.toList}"
  logInfo s!"bounds:\n{String.intercalate "\n" boundLines.toList}"
  unless sites.size == 6 do throwError "the six punts moved under this pass: sites={sites.size}"
  check "expectedSites" siteLines expectedSites
  check "expectedShapes" shapeLines expectedShapes
  check "expectedBounds" boundLines expectedBounds
  unless got == expectedLine do
    throwError "PuntCoverInputs moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.PuntCoverInputs
