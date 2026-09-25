/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ValueLinePacks

/-!
# Where the value-line packs are born: every writer row's chain resolved to its origins, and the tail there (DOCS item 262)

Item 261 read, at each of the value-line packs' writer positions, what the
writer holds toward a `SCompactMapTail` at the level it writes, and found
the tail in hand at eleven of the sixty-nine that build, re-wrap or
transport a pack.  A re-wrap holds what its caller handed it: whether a
`none` row is a real absence depends on where its chain is BORN — the
position that first builds the pack from a route or a frames face — and on
whether the tail is in hand THERE.  This module resolves every row to its
origins.

**§0** finds the pack positions as item 261 did, by shape, and one
unfolding deeper: a parameter or field whose type carries the value closure
inside an L4YAML `Prop` definition or single-constructor `Prop` structure
(`ImplicitKeyPack`, `PropsKeyPack`) is a position too, listed `packaged`;
every position gets the PATH from its type to the closure (through the
option's arm, the existentials, the conjunctions, the guards and the
unfolding).  **§1** re-runs item 261's walk over the extended positions and,
at every row, reads the argument's BOTTOMS structurally: the hypotheses the
pack's closure is built from, navigating the term along the position's
path, through matches, casts, transports (lemmas whose conclusion carries
the stream, a frames face or a pack) and constructors.  **§2** follows each
bottom inside its lemma: a pack parameter's or park field's label is an
edge to that POSITION; a route, frames or tail hypothesis is an ORIGIN at
the row; a `let` is followed into its value; a local function's parameter
is resolved through the function's applications; a match's pattern variable
through its discriminant.  **§3** resolves positions by the least fixpoint
over the producer relation (the rows whose target is the position), so a
family whose producers are only punts and relays of each other resolves to
NOTHING: its honest arms are `unborn`.  At every origin the tail reading is
item 261's at the origin row, and for a route origin also at the route's own
level.

The pins hold the positions, the origins, every row's resolution, the
per-position summary, the unborn positions and the line.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropDependents (sorted)
open Tests.Guards.RouteShapes
open Tests.Guards.StreamCompositions
open Tests.Guards.CloseSplitFrames
open Tests.Guards.CloseStackCover
open Tests.Guards.PuntCoverInputs
open Tests.Guards.ValueLinePacks

namespace Tests.Guards.ValueLineOrigins

/-! ## §0 Packaged packs and the path to the closure -/

/-- The environment with the constants that package a value closure: every
    L4YAML `Prop` definition whose body carries it outside a `ResumeFrames`
    (`ImplicitKeyPack`, `PropsKeyPack`).  A `Prop` structure's fields are not
    unfolded: the flow base's routes (`FlowBaseRoutes`) travel in the
    flow-stack invariant, which this census does not follow. -/
structure PackEnv where
  env : Environment
  packConsts : Std.HashSet Name

def mkPackEnv (env : Environment) : PackEnv := Id.run do
  let mut s : Std.HashSet Name := {}
  for (c, ci) in env.constants.toList do
    if c.getRoot != `L4YAML || c == resumeN || c == evlN then continue
    match ci with
    | .defnInfo di => if (piConcl di.type).isProp && vcOutside di.value then s := s.insert c
    | _ => pure ()
  return { env, packConsts := s }

/-- A structure's constructor telescope with its conclusion (the structure
    itself, applied) cut to `True`, so an unfolding never re-enters it. -/
partial def cutConcl (t : Expr) : Expr :=
  match t with
  | .forallE n ty b bi => .forallE n ty (cutConcl b) bi
  | _ => mkConst ``True

/-- One unfolding of a packaging constant applied to arguments: the body the
    arguments instantiate (a structure's fields, their conclusion cut). -/
def unfoldPack (pe : PackEnv) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  match e.getAppFn with
  | .const c _ =>
    if !pe.packConsts.contains c then none
    else match pe.env.find? c with
      | some (.defnInfo di) => some (di.value.beta e.getAppArgs)
      | some (.inductInfo iv) =>
        if iv.numParams ≤ e.getAppNumArgs then
          match pe.env.find? iv.ctors[0]! with
          | some (.ctorInfo cv) => Id.run do
            let mut ty := cv.type
            let args := e.getAppArgs
            for i in [0:cv.numParams] do
              match ty with
              | .forallE _ _ b _ => ty := b.instantiate1 args[i]!
              | _ => break
            return some (cutConcl ty)
          | _ => none
        else none
      | _ => none
  | _ => none

/-- The value closure, directly or inside a packaging constant, outside any
    `ResumeFrames`. -/
partial def vcDeep (pe : PackEnv) (e : Expr) : Bool :=
  let e := e.consumeMData
  if isValueClosure e || e.isAppOf evlN then true
  else if e.isAppOf resumeN then false
  else match e with
    | .const c _ => pe.packConsts.contains c
    | .app f a => vcDeep pe f || vcDeep pe a
    | .forallE _ t b _ => vcDeep pe t || vcDeep pe b
    | .lam _ t b _ => vcDeep pe t || vcDeep pe b
    | .letE _ t v b _ => vcDeep pe t || vcDeep pe v || vcDeep pe b
    | .proj _ _ b => vcDeep pe b
    | _ => false

inductive VStep | orL | orR | ex | andL | andR | unfold | imp
  deriving BEq, Repr, Inhabited, Hashable

def VStep.render : VStep → String
  | .orL => "∨L" | .orR => "∨R" | .ex => "∃" | .andL => "∧L" | .andR => "∧R" | .unfold => "δ" | .imp => "→"

def renderVPath (p : List VStep) : String := String.intercalate "" (p.map VStep.render)

/-- The path from a position's type to its value closure: the option's arm,
    the existentials, the conjunctions (the right side first, as item 261
    read them), the closure's own binders as `→`, and an unfolding. -/
partial def vcPath (pe : PackEnv) (t : Expr) (fuel : Nat := 96) : List VStep :=
  let t := t.consumeMData
  if fuel == 0 then []
  else if isValueClosure t || t.isAppOf evlN then []
  else if t.isAppOfArity ``Or 2 then
    if vcDeep pe (t.getArg! 0) then .orL :: vcPath pe (t.getArg! 0) (fuel - 1) else .orR :: vcPath pe (t.getArg! 1) (fuel - 1)
  else if t.isAppOfArity ``Exists 2 then
    match (t.getArg! 1).consumeMData with
    | .lam _ _ b _ => .ex :: vcPath pe b (fuel - 1)
    | _ => []
  else if t.isAppOfArity ``And 2 then
    if vcDeep pe (t.getArg! 1) then .andR :: vcPath pe (t.getArg! 1) (fuel - 1) else .andL :: vcPath pe (t.getArg! 0) (fuel - 1)
  else match t with
    | .forallE _ _ b _ => .imp :: vcPath pe b (fuel - 1)
    | _ => match unfoldPack pe t with
      | some b => .unfold :: vcPath pe b (fuel - 1)
      | none => []

/-- Item 261's `peelToClosure` through packaged definitions: the stack at
    the closure, the closure, and the level binding read on the way. -/
partial def peelD (pe : PackEnv) (st : Stack) (t : Expr) (lvl : Array String) (fuel : Nat := 96) : Stack × Expr × Array String :=
  let t := t.consumeMData
  if fuel == 0 then (st, t, lvl)
  else if vcOutside t then
    let (st', cl, lvl') := peelToClosure st t #[]
    (st', cl, lvl ++ lvl')
  else if t.isAppOfArity ``Or 2 then
    if vcDeep pe (t.getArg! 0) then peelD pe st (t.getArg! 0) lvl (fuel - 1) else peelD pe st (t.getArg! 1) lvl (fuel - 1)
  else if t.isAppOfArity ``Exists 2 then
    match (t.getArg! 1).consumeMData with
    | .lam n ty b _ => peelD pe (st.push { name := n, ty, prov := none }) b (lvl.push s!"∃{bname n}") (fuel - 1)
    | _ => (st, t, lvl)
  else if t.isAppOfArity ``And 2 then
    if vcDeep pe (t.getArg! 1) then peelD pe st (t.getArg! 1) (lvl.push s!"({propTok st (t.getArg! 0)})") (fuel - 1)
    else peelD pe st (t.getArg! 0) (lvl.push s!"({propTok st (t.getArg! 1)})") (fuel - 1)
  else match t with
    | .forallE n ty b _ => peelD pe (st.push { name := n, ty, prov := none }) b (lvl.push s!"({propTok st ty})→") (fuel - 1)
    | _ => match unfoldPack pe t with
      | some b => peelD pe st b (lvl.push s!"δ{short t.getAppFn.constName!}") (fuel - 1)
      | none => (st, t, lvl)

/-- Which arm carries the closure (packaging seen through), and whether the
    other arm is `True`. -/
def sideOfD (pe : PackEnv) (t : Expr) : Bool × Bool :=
  let t := t.consumeMData
  if t.isAppOfArity ``Or 2 then
    let vcLeft := vcDeep pe (t.getArg! 0)
    let other := (if vcLeft then t.getArg! 1 else t.getArg! 0).consumeMData
    (vcLeft, other.isConstOf ``True)
  else (true, true)

structure Position where
  key : String
  kind : String
  owner : Name
  idx : Nat
  name : Name
  path : List VStep
  vcLeft : Bool
  otherTrue : Bool
  packaged : Bool
  line : String
  deriving Inhabited

structure Cands where
  cd : PCand := {}
  positions : Array Position := #[]
  thms : Array Name := #[]

/-- A position's shape line: its level binding, premise chain and where the
    tail stands (after the value, before it, or nowhere). -/
def shapeLine (pe : PackEnv) (stk : Stack) (t : Expr) : String :=
  let (st', cl, lvl) := peelD pe stk t #[]
  let (prems, concl, tail) := premisesOf pe.env st' cl #[] false false
  let before := prems.any (·.startsWith "SCompactMapTail")
  s!"lvl={String.intercalate "" lvl.toList} premises=[{String.intercalate "," prems.toList}] ⊢ {concl} tail={if tail then "after" else if before then "before" else "no"}"

def mkPosition (pe : PackEnv) (kind : String) (owner : Name) (idx : Nat) (n : Name) (stk : Stack) (t : Expr) : Position :=
  let (vcLeft, otherTrue) := sideOfD pe t
  let packaged := !vcOutside t
  let path := vcPath pe t
  let key := s!"{kind}:{short owner}.{n}"
  { key, kind, owner, idx, name := n, path, vcLeft, otherTrue, packaged,
    line := s!"{key}{if packaged then " packaged" else ""} arm={if vcLeft then "l" else "r"}{if otherTrue then "" else "/stamp"} path={renderVPath path} {shapeLine pe stk t}" }

/-- The positions: the park fields and the lemma parameters that carry the
    value closure, directly or packaged. -/
def collect (pe : PackEnv) : MetaM Cands := do
  let env := pe.env
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let mut cs : Cands := {}
  for c in iv.ctors do
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut i := 0
    let mut stk : Stack := #[]
    let mut names : Array Name := #[]
    let mut packs : Array Pos := #[]
    while true do
      match ty with
      | .forallE n t b _ =>
        if i ≥ cv.numParams then
          names := names.push n
          if vcDeep pe t then
            let p := mkPosition pe "ctor" c i n stk t
            packs := packs.push (i, n, p.vcLeft, p.otherTrue)
            cs := { cs with positions := cs.positions.push p }
        stk := stk.push { name := n, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    cs := { cs with cd := { cs.cd with ctors := cs.cd.ctors.insert c, fieldNames := cs.cd.fieldNames.insert c names, packs := cs.cd.packs.insert c packs, consts := cs.cd.consts.insert c } }
  cs := { cs with cd := { cs.cd with consts := cs.cd.consts.insert ``PendingNode.casesOn } }
  let mut paramPos : Array Position := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML then continue
    unless ci matches .thmInfo _ do continue
    cs := { cs with thms := cs.thms.push n }
    let mut ty := ci.type
    let mut i := 0
    let mut stk : Stack := #[]
    let mut ps : Array Pos := #[]
    while true do
      match ty with
      | .forallE pn t b _ =>
        if vcDeep pe t then
          let p := mkPosition pe "param" n i pn stk t
          ps := ps.push (i, pn, p.vcLeft, p.otherTrue)
          paramPos := paramPos.push p
        stk := stk.push { name := pn, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    if !ps.isEmpty then cs := { cs with cd := { cs.cd with lemParams := cs.cd.lemParams.insert n ps, consts := cs.cd.consts.insert n } }
  paramPos := paramPos.qsort (·.key < ·.key)
  return { cs with positions := cs.positions ++ paramPos }

/-! ## §1 The bottoms of a pack argument -/

/-- A hypothesis the pack's closure bottoms in (with the stack it stands
    in, the arguments it is applied to and the path left to the closure), or
    a terminal. -/
inductive Bot
  | bind (b : Bind) (depth : Nat) (st : Stack) (args : Array Expr) (rest : List VStep)
  | term (s : String)
  deriving Inhabited

def isPuntTerm (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isConstOf ``trivial || e.isConstOf ``True.intro

/-- The name of the `j`-th leading lambda binder. -/
partial def lamName (e : Expr) (j : Nat) : Option Name :=
  match e.consumeMData with
  | .lam n _ b _ => if j == 0 then some n else lamName b (j - 1)
  | _ => none

/-- The type of the `j`-th leading lambda binder. -/
partial def lamTy (e : Expr) (j : Nat) : Option Expr :=
  match e.consumeMData with
  | .lam _ t b _ => if j == 0 then some t else lamTy b (j - 1)
  | _ => none

/-- The kind of a hypothesis, packaging seen through. -/
def kindOf (pe : PackEnv) (b : Bind) : String :=
  if vcDeep pe b.ty then "chain" else bindKind (some b)

/-- The level named by the first surface premise of a hypothesis. -/
partial def lvlOf (env : Environment) (st : Stack) (t : Expr) : Option String :=
  let t := t.consumeMData
  let own : Option String := match t.getAppFn with
    | .const h _ => if (`L4YAML.Surface).isPrefixOf h && t.getAppNumArgs ≥ 1 && levelFirst env h then some (ppc st (t.getArg! 0)) else none
    | _ => none
  match t with
  | .forallE n ty b _ =>
    (lvlOf env st ty).orElse fun _ => lvlOf env (st.push { name := n, ty, prov := none }) b
  | .app .. =>
    if t.isAppOfArity ``Or 2 || t.isAppOfArity ``And 2 || t.isAppOfArity ``Exists 2 then
      t.getAppArgs.findSome? fun a => lvlOf env st a
    else own
  | .lam n ty b _ => lvlOf env (st.push { name := n, ty, prov := none }) b
  | _ => none

/-- A lemma whose conclusion carries the stream, a frames face or a pack, or
    a predicate it is polymorphic in (`frameChainOne`'s `P x`): one a pack's
    closure can be built through. -/
def isTransport (pe : PackEnv) (m : Name) : Bool :=
  match pe.env.find? m with
  | some (.thmInfo ti) =>
    let c := piConcl ti.type
    hasHead c streamN || hasHead c resumeN || vcDeep pe c || (c.find? fun s => s.isApp && s.getAppFn.isBVar).isSome
  | _ => false

abbrev BMemo := IO.Ref (Std.HashMap (Expr × Nat × List VStep) (Array Bot))

/-- The matches the bottoms reader enters (their alternative binders are
    labeled from the discriminants), for the follower to resolve. -/
abbrev DynAlts := IO.Ref (Array AltRec)

/-- A visit budget per row: the reader stops with a `budget` terminal past it. -/
abbrev Budget := IO.Ref Nat


/-- Every hypothesis the argument's closure is built from, navigating the
    term along the position's path. -/
partial def bottomsOf (pe : PackEnv) (memo : BMemo) (budget : Budget) (dyn : DynAlts) (st : Stack) (e : Expr) (path : List VStep) (fuel : Nat := 40) : MetaM (Array Bot) := do
  if fuel == 0 then return #[.term "fuel"]
  if (← budget.get) == 0 then return #[.term "budget"]
  budget.modify (· - 1)
  let e := peelSafe e
  if let some r := (← memo.get)[(e, st.size, path)]? then return r
  let r ← go e
  memo.modify (·.insert (e, st.size, path) r)
  return r
where
  go (e : Expr) : MetaM (Array Bot) := do
  let env := pe.env
  match e with
  | .lam n t b _ =>
    let path' := match path with | .imp :: r => r | p => p
    bottomsOf pe memo budget dyn (st.push { name := n, ty := t, prov := none }) b path' fuel
  | .bvar i =>
    if i < st.size then return #[.bind st[st.size - 1 - i]! (st.size - 1 - i) st #[] path] else return #[.term "#?"]
  | .const c _ => if isPuntTerm e then return #[.term "punt"] else return #[.term s!"?{short c}"]
  | .proj _ _ b => bottomsOf pe memo budget dyn st b path (fuel - 1)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .bvar i =>
      if i < st.size then return #[.bind st[st.size - 1 - i]! (st.size - 1 - i) st args path] else return #[.term "#?"]
    | .const c _ =>
      if let some (_, discrs, brs) ← branchesOf c args then
        dyn.modify (·.push { lem := .anonymous, st, discrs })
        let lab ← altLabeler st discrs
        let mut out : Array Bot := #[]
        for b in brs do
          let (st', body) := enterAllF st lab args[b]!
          out := out ++ (← bottomsOf pe memo budget dyn st' body path (fuel - 1))
        return out
      if deadEnd c then return #[.term "absurd"]
      let other (x : Expr) : Array Bot := #[.term (if isPuntTerm x then "punt" else "stamp")]
      if c == ``Or.inl && args.size ≥ 3 then
        match path with
        | .orL :: r => return ← bottomsOf pe memo budget dyn st args[2]! r (fuel - 1)
        | .orR :: _ => return other args[2]!
        | _ => return ← bottomsOf pe memo budget dyn st args[2]! path (fuel - 1)
      if c == ``Or.inr && args.size ≥ 3 then
        match path with
        | .orR :: r => return ← bottomsOf pe memo budget dyn st args[2]! r (fuel - 1)
        | .orL :: _ => return other args[2]!
        | _ => return ← bottomsOf pe memo budget dyn st args[2]! path (fuel - 1)
      if c == ``Exists.intro && args.size ≥ 4 then
        let r := match path with | .ex :: r => r | p => p
        return ← bottomsOf pe memo budget dyn st args[3]! r (fuel - 1)
      if c == ``And.intro && args.size ≥ 4 then
        match path with
        | .andL :: r => return ← bottomsOf pe memo budget dyn st args[2]! r (fuel - 1)
        | .andR :: r => return ← bottomsOf pe memo budget dyn st args[3]! r (fuel - 1)
        | _ => return ← bottomsOf pe memo budget dyn st args[3]! path (fuel - 1)
      if c == ``Or.imp && args.size ≥ 7 then return ← bottomsOf pe memo budget dyn st args[6]! path (fuel - 1)
      if (c == ``Or.imp_left || c == ``Or.imp_right) && args.size ≥ 5 then return ← bottomsOf pe memo budget dyn st args[4]! path (fuel - 1)
      if (c == ``And.left || c == ``And.right) && args.size ≥ 3 then return ← bottomsOf pe memo budget dyn st args[2]! path (fuel - 1)
      if (← getProjectionFnInfo? c).isSome && args.size ≥ 1 then return ← bottomsOf pe memo budget dyn st args[args.size - 1]! path (fuel - 1)
      if c.getRoot == `L4YAML && (isTransport pe c || (isCtorN env c && !(`L4YAML.Surface).isPrefixOf c)) then
        let mut out : Array Bot := #[]
        for a in args do
          let a' := peelSafe a
          let cand := match a' with
            | .lam .. => !isPredLam a'
            | .bvar .. => (match bindOf st a' with
                | some b => !isDataTy b.ty && (kindOf pe b != "other" || hasHead b.ty streamN || hasHead b.ty resumeN || hasHead b.ty tailN)
                | none => false)
            | .app .. => (match a'.getAppFn with
                | .bvar _ => true
                | .const m _ => (m.getRoot == `L4YAML && (isTransport pe m || (isCtorN env m && !(`L4YAML.Surface).isPrefixOf m))) || m == ``Or.inl || m == ``Or.inr ||
                    m == ``Exists.intro || m == ``And.intro || m == ``And.left || m == ``And.right || m == ``Or.imp ||
                    (Lean.Meta.Match.Extension.getMatcherInfo? env m).isSome || isCasesOnRecursor env m ||
                    m == ``dite || m == ``ite || m == ``Or.elim || m == ``Exists.elim || m == ``Or.rec || m == ``Decidable.byCases
                | _ => false)
            | .proj .. => true
            | _ => false
          if cand then out := out ++ (← bottomsOf pe memo budget dyn st a' [] (fuel - 1))
        let live := out.filter fun
          | .term s => !(s == "absurd" || s == "punt" || s == "stamp" || s.startsWith "?" || s == "#?")
          | _ => true
        if live.isEmpty then return #[.term s!"{if isCtorN env c then "ctor" else "concl"}:{short c}"]
        return live
      -- a lemma whose conclusion carries no stream and no pack proves a side
      -- fact (a guard, a scanner predicate): not a source
      if c.getRoot == `L4YAML && isThmN env c then return #[.term s!"fact:{short c}"]
      return #[.term s!"?{short c}"]
    | _ => return #[.term "?"]
  | _ => return #[.term "?"]

/-! ## §2 Following a bottom inside its lemma -/

/-- Where a bottom leads: a position (another producer's row set), an
    origin at this row, a dead end the follower cannot read, or nothing
    (a punt, a stamp, an absurd branch). -/
inductive Src
  | pos (key : String)
  | origin (kind : String) (label : String) (lvl : Option String)
  | dead (why : String)
  /-- No source: a punt, a stamp, an absurd branch, a side fact. -/
  | none (why : String)
  deriving Inhabited, BEq

abbrev FMemo := IO.Ref (Std.HashMap (Name × Nat × String × List VStep × Array Expr) (Array Src))

structure FCx where
  pe : PackEnv
  memo : BMemo
  budget : Budget
  dyn : DynAlts
  fmemo : FMemo
  lem : Name
  posKeys : Std.HashSet String
  lets : Array LetRec
  lapps : Array LApp
  alts : Array AltRec

def dedupSrc (xs : Array Src) : Array Src := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

mutual
partial def followBot (cx : FCx) (bot : Bot) (fuel : Nat := 8) : MetaM (Array Src) := do
  match bot with
  | .term s =>
    if s == "punt" || s == "stamp" || s == "absurd" then return #[.none s]
    if s.startsWith "fact:" then return #[.none "fact"]
    if s.startsWith "concl:" || s.startsWith "ctor:" then return #[.origin "concl" s none]
    return #[.dead s]
  | .bind b depth st args rest =>
    let key := (cx.lem, depth, b.prov.getD "", rest, args)
    if let some r := (← cx.fmemo.get)[key]? then return r
    let r ← followBind cx b depth st args rest fuel
    let r := dedupSrc r
    cx.fmemo.modify (·.insert key r)
    return r

partial def followBind (cx : FCx) (b : Bind) (depth : Nat) (st : Stack) (args : Array Expr) (rest : List VStep) (fuel : Nat) : MetaM (Array Src) := do
    let kind := kindOf cx.pe b
    let lvl := lvlOf cx.pe.env (st.extract 0 depth) b.ty
    -- a relational invariant (an L4YAML inductive: the flow stack's interior,
    -- a pending node) is an origin of its own kind; a side fact (a column,
    -- an equation, a scanner predicate) is not a source
    let invHead : Option Name := match (piConcl b.ty).getAppFn with
      | .const h _ => (match cx.pe.env.find? h with
        | some (.inductInfo _) => if h.getRoot == `L4YAML && !(`L4YAML.Surface).isPrefixOf h then some h else none
        | _ => none)
      | _ => none
    if kind == "other" && !(hasHead b.ty streamN || hasHead b.ty resumeN || hasHead b.ty tailN || vcDeep cx.pe b.ty) then
      if let some h := invHead then return #[.origin "invariant" s!"{short h}@{b.prov.getD (bname b.name)}" lvl]
      return #[.none "fact"]
    match b.prov with
    | none => return #[.dead s!"own:{bname b.name}"]
    | some p =>
      if fuel == 0 then return #[.dead s!"fuel@{p}"]
      if p.startsWith "param:" then
        if kind == "chain" && cx.posKeys.contains p then return #[.pos p] else return #[.origin kind p lvl]
      if p.startsWith "door:" then
        let key := "ctor:" ++ (p.drop 5).toString
        if kind == "chain" && cx.posKeys.contains key then return #[.pos key] else return #[.origin kind p lvl]
      if p.startsWith "let:" then
        let ls := cx.lets.filter fun l => l.label == p
        if ls.isEmpty then return #[.dead s!"let?{p}"]
        let mut out : Array Src := #[]
        for l in ls do out := out ++ (← followLet cx l st args (fuel - 1))
        return out
      if p.startsWith "λ:" then
        let mut out : Array Src := #[]
        let mut found := false
        for l in cx.lets do
          unless l.st.size ≤ depth do continue
          let j := depth - l.st.size
          if lamName l.val j == some b.name then
            found := true
            let path := match lamTy l.val j with | some t => vcPath cx.pe t | none => rest
            for a in cx.lapps do
              unless a.head.name == l.name && a.head.prov == some l.label do continue
              if j < a.args.size then
                for bt in (← bottomsOf cx.pe cx.memo cx.budget cx.dyn a.st a.args[j]! path) do out := out ++ (← followBot cx bt (fuel - 1))
              else out := out.push (.dead s!"{p} partial")
        if found then return out else return #[.dead p]
      let mut out : Array Src := #[]
      let mut found := false
      for a in cx.alts ++ (← cx.dyn.get) do
        unless a.st.size ≤ depth do continue
        for d in a.discrs do
          if (← sourceOf a.st d) == some p then
            found := true
            -- a discriminant that is itself a lemma's conclusion: the pack
            -- is built by that lemma, an origin here
            if p.startsWith "ret:" && !(d.consumeMData.isBVar) then
              let bots ← bottomsOf cx.pe cx.memo cx.budget cx.dyn a.st d rest
              let live := bots.filter fun | .term t => !(t.startsWith "?") | _ => true
              if live.isEmpty then out := out.push (.origin "concl" p lvl)
              else for bt in live do out := out ++ (← followBot cx bt (fuel - 1))
            else
              let path := match bindOf a.st d with | some db => vcPath cx.pe db.ty | none => rest
              for bt in (← bottomsOf cx.pe cx.memo cx.budget cx.dyn a.st d path) do out := out ++ (← followBot cx bt (fuel - 1))
      if found then return out
      if p.startsWith "ret:" then return #[.origin "concl" p lvl]
      return #[.dead p]

/-- Into a `let`'s value: its bottoms, a local function's parameters
    mapped to the arguments at the application the bottom came from. -/
partial def followLet (cx : FCx) (l : LetRec) (appSt : Stack) (args : Array Expr) (fuel : Nat) : MetaM (Array Src) := do
  let bots ← bottomsOf cx.pe cx.memo cx.budget cx.dyn l.st l.val (vcPath cx.pe l.ty)
  let mut out : Array Src := #[]
  for bt in bots do
    match bt with
    | .bind b d _ _ _ =>
      if b.prov.isNone && d ≥ l.st.size && d - l.st.size < args.size then
        let path := match lamTy l.val (d - l.st.size) with | some t => vcPath cx.pe t | none => []
        for b2 in (← bottomsOf cx.pe cx.memo cx.budget cx.dyn appSt args[d - l.st.size]! path) do out := out ++ (← followBot cx b2 (fuel - 1))
      else out := out ++ (← followBot cx bt (fuel - 1))
    | _ => out := out ++ (← followBot cx bt (fuel - 1))
  return out
end

/-! ## §3 The pins -/

def pinned : Bool := true
def expectedPositions : List String := [
  "ctor:pendingContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(?)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "ctor:pendingContent.h_vpack arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingProps.h_key packaged arm=l/stamp path=∨Lδ∧L∃∧R∧R∧L∨L∃→→→→→→→→→→ lvl=δPropsKeyPack(And)∃k(?)(col(…)=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "ctor:pendingProps.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockNode(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingProps.h_kslotE arm=l path=∨L∃∃∧R→→→→→→→→ lvl=∃ne∃nv(n=ne + 1) premises=[SBlockNode(n),SCompactSeqTail(ne),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingBlockContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(?)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "ctor:pendingBlockContent.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃nv premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingBlockContent.h_kslotUp arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingBlock.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃nv premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingBlock.h_kslotUp arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingMapValue.h_ivl arm=r/stamp path=∨R∧R lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "ctor:pendingMapValue.h_vslot arm=l path=∨L∧R∧R lvl=(sc.currentIndent≤n)(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "ctor:pendingMapValue.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "ctor:pendingMapValue.h_explUp arm=l path=∨L∃∃∧R→→→→→→→→ lvl=∃sp_q∃ns(GLit('?'))∀nv∈ns premises=[SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_block_on_closeThenBlock.h_vpack arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_block_on_closeThenBlock.h_vslot arm=l path=∨L∃∃∧R∧R∧R∧R∧R∧R∧R∨L∃→→→→→→→→ lvl=∃nv∃sp_a(SLYamlStream(sp_start))(sc.currentIndent≤nv)(needIndentCheck(…)=false)(simpleKeyAllowed(…)=true)(sp_scan.col=nv + 1)(?)(Or)∃nsU∀nvU∈nsU premises=[SBlockIndented(nv),SIndent(nvU),GLit(':'),SBlockIndented(nvU)] ⊢ SLYamlStream tail=no",
  "param:accum_block_on_pendingBlock.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃nv premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_block_on_pendingBlock.h_kslotUp arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_block_on_pendingBlockContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(?)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "param:accum_block_on_pendingBlockContent.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃nv premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_block_on_pendingBlockContent.h_kslotUp arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_block_on_pendingContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(?)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "param:accum_block_on_pendingContent.h_vpack arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_content_on_pendingBlock_indented.h_kslotUp_old arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_content_on_pendingBlock_indented.h_kslot_old arm=l path=∨L∃→→→→→→→→ lvl=∃nv premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_content_on_pendingMapValue_indented.h_ivl_mv arm=r/stamp path=∨R∧R lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "param:accum_content_on_pendingMapValue_indented.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:accum_content_on_pendingMapValue_indented.h_vslot arm=l path=∨L∧R lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "param:colon_fires_implicit_key.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(?)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "param:colon_fires_props_key.h_key packaged arm=l/stamp path=∨Lδ∧L∃∧R∧R∧L∨L∃→→→→→→→→→→ lvl=δPropsKeyPack(And)∃k(?)(col(…)=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "param:colon_open_map_explicit.hvp arm=l path=→→→→→→ lvl= premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:colon_open_map_implicit.h_kslot arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "param:colon_open_map_props.h_kslot arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "param:entryChainMap.up arm=l path=→→→→→→ lvl=∀nvX∈ns premises=[SBlockIndented(n),SCompactSeqTail(n)] ⊢ ExplValueLine(nvX) tail=no",
  "param:entryKeyPack_of_dispatch.h_compact arm=l path=∨L∧R∧R∨L∃→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:entryKeyPack_of_dispatch.h_ivl arm=r/stamp path=∨R∧R∧R∨L∃→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:entryKeyPack_of_dispatch.h_nodeV arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:entryPropsKeyPack_of_dispatch.h_compact arm=l path=∨L∧R∧R∨L∃→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:entryPropsKeyPack_of_dispatch.h_ivl arm=r/stamp path=∨R∧R∧R∨L∃→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:entryPropsKeyPack_of_dispatch.h_nodeV arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:explFrameValueLine.h_kslot arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:flowKeyPack_of_close.h_key arm=l path=∨L∃∃∧R∧R∧R∧L∨L∃→→→→→→→→→→ lvl=∃k∃sp_key(?)(?)(kc=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=before",
  "param:flowKeyRoute_of_open.h_compact_pair arm=l path=∨L∃∃→→→→→→→→ lvl=∃nv0∃ns∀nv∈nv0 :: ns premises=[SBlockIndented(nc),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:flowVPack_of_close.h_vslot arm=l path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SFlowContent(n),SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:indicator_open_map.h_explUp_chain arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:question_open_map.h_explUp_chain arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "param:slotChainMap.up arm=l path=→→→→ lvl=∀nvX∈ns premises=[SBlockIndented(nv)] ⊢ ExplValueLine(nvX) tail=no"]
def expectedOrigins : List String := [
  "O0 accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vpack ← route(door:pendingMapValue.h_expl) lvl=nmv ⊢ held(h_closeF155,h_seqF✝) | @nmv:held(h_closeF155,h_seqF✝) → held",
  "O1 accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O2 accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeF_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O3 accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_entry_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O4 accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O5 accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeF_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O6 accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O7 accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeF_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O8 accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_entry_old) lvl=n ⊢ held(h_closeF_old,h_closeFV_old) | @n:none → unheld",
  "O9 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← route(param:accum_content_on_pendingMapValue_indented.h_close_old) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → unheld",
  "O10 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← other(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n:held(h_closeF99,h_seqF168) → held",
  "O11 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeF99) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O12 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_frames99) lvl=— ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) → held",
  "O13 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeFV108) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O14 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_framesV108) lvl=— ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) → held",
  "O15 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_seqF168) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O16 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_vpack ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_closeF99,h_seqF168) | @n:held(h_closeF99,h_seqF168) → held",
  "O17 accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_nodeV ← other(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → unheld",
  "O18 accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_compact ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → held",
  "O19 accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_ivl ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → held",
  "O20 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← route(param:accum_content_on_pendingMapValue_indented.h_close_old) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → unheld",
  "O21 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← other(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n:held(h_closeF99,h_seqF168) → held",
  "O22 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeF99) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O23 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_frames99) lvl=— ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) → held",
  "O24 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeFV108) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O25 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_framesV108) lvl=— ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) → held",
  "O26 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslot ← other(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ none | @n:held(h_closeF99,h_seqF168) → unheld",
  "O27 accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV ← other(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → unheld",
  "O28 accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → held",
  "O29 accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → held",
  "O30 accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_vpack ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_closeF99,h_seqF168) | @n:held(h_closeF99,h_seqF168) → held",
  "O31 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← route(param:accum_content_on_pendingMapValue_indented.h_close_old) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → unheld",
  "O32 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← other(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n:held(h_closeF99,h_seqF168) → held",
  "O33 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeF99) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O34 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_frames99) lvl=— ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) → held",
  "O35 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeFV108) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O36 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_framesV108) lvl=— ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) → held",
  "O37 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_seqF168) lvl=n + 1 ⊢ held(h_closeF99,h_frames99,h_closeFV108,h_framesV108,h_seqF168) | @n + 1:none → held",
  "O38 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_vpack ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_closeF99,h_seqF168) | @n:held(h_closeF99,h_seqF168) → held",
  "O39 accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_nodeV ← other(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → unheld",
  "O40 accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_compact ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → held",
  "O41 accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_ivl ← route(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_closeF99,h_seqF168) → held",
  "O42 accum_flow_open_depth0 #3 param:flowKeyRoute_of_open.h_compact_pair ← route(door:pendingMapValue.h_expl) lvl=n_old ⊢ held(h_closeF✝,h_seqF✝) | @n_old:held(h_closeF✝,h_seqF✝) → held",
  "O43 accum_step_flow #1 ctor:pendingContent.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O44 accum_step_flow #1 ctor:pendingContent.h_vpack ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O45 accum_step_flow #1 param:flowKeyPack_of_close.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O46 accum_step_flow #1 param:flowVPack_of_close.h_vslot ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O47 accum_step_flow #2 ctor:pendingContent.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O48 accum_step_flow #2 ctor:pendingContent.h_vpack ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O49 accum_step_flow #2 param:flowKeyPack_of_close.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O50 accum_step_flow #2 param:flowVPack_of_close.h_vslot ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O51 colon_open_map #1 ctor:pendingMapValue.h_kslot ← frames(param:colon_open_map.h_resV_land) lvl=k ⊢ none | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → unheld",
  "O52 compact_open_map #1 ctor:pendingMapValue.h_ivl ← route(param:compact_open_map.h_close_old) lvl=n ⊢ none | @n:none → unheld",
  "O53 compact_open_map #1 ctor:pendingMapValue.h_vslot ← route(param:compact_open_map.h_close_old) lvl=n ⊢ none | @n:none → unheld",
  "O54 content_dispatch_routed #1 ctor:pendingContent.h_key ← frames(param:content_dispatch_routed.h_resumectx) lvl=k ⊢ level-var | @k:none → unheld",
  "O55 content_dispatch_routed #2 ctor:pendingContent.h_key ← frames(param:content_dispatch_routed.h_resumectx) lvl=k ⊢ level-var | @k:none → unheld",
  "O56 question_open_map #1 ctor:pendingMapValue.h_ivl ← frames(param:question_open_map.h_nodoc_land) lvl=k ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O57 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:suffixMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O58 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:nodocMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O59 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:markerMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O60 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:propsMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O61 question_open_map #1 ctor:pendingMapValue.h_ivl ← route(param:question_open_map.h_stream_land) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O62 question_open_map #1 ctor:pendingMapValue.h_vslot ← frames(param:question_open_map.h_nodoc_land) lvl=k ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O63 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:suffixMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O64 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:nodocMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O65 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:markerMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O66 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:propsMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O67 question_open_map #1 ctor:pendingMapValue.h_vslot ← route(param:question_open_map.h_stream_land) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → held",
  "O68 question_open_map #1 ctor:pendingMapValue.h_kslot ← frames(param:question_open_map.h_resV_land) lvl=k ⊢ level-var | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → unheld",
  "O69 question_open_map #1 ctor:pendingMapValue.h_explUp ← frames(param:question_open_map.h_resV_land) lvl=k ⊢ level-var | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF) → unheld"]
def expectedRows : List String := [
  "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslot := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #1 param:indicator_open_map.h_explUp_chain := alt/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #1 param:slotChainMap.up := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #2 param:slotChainMap.up := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] none=[absurd] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #3 param:slotChainMap.up := relay/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #1 param:colon_open_map_explicit.hvp := relay/built pos=[param:accum_block_on_closeThenBlock.h_vpack] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ some-held 21/42",
  "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslot := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_noPending #1 ctor:pendingBlock.h_kslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_noPending #1 ctor:pendingBlock.h_kslotUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_noPending #1 param:indicator_open_map.h_explUp_chain := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslot := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslot := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingBlock #1 param:indicator_open_map.h_explUp_chain := alt/built pos=[param:accum_block_on_pendingBlock.h_kslotUp,param:accum_block_on_pendingBlock.h_kslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:entryChainMap.up := via/built pos=[param:accum_block_on_pendingBlock.h_kslotUp,param:accum_block_on_pendingBlock.h_kslot] origins=[O69] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #2 param:entryChainMap.up := via/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[O69] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #3 param:entryChainMap.up := relay/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O69] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:colon_open_map_explicit.hvp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslot,param:accum_block_on_pendingBlock.h_kslotUp] origins=[O69] none=[stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslot := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslot := paid:chain/built pos=[param:accum_block_on_pendingBlockContent.h_kslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlockContent.h_kslotUp] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingBlockContent #1 param:indicator_open_map.h_explUp_chain := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingBlockContent #1 param:colon_open_map_explicit.hvp := paid:chain/built pos=[param:accum_block_on_pendingBlockContent.h_kslot,param:accum_block_on_pendingBlockContent.h_kslotUp] origins=[O69] none=[stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlockContent #1 param:colon_fires_implicit_key.h_key := relay/built pos=[param:accum_block_on_pendingBlockContent.h_key] origins=[O1,O2,O3,O6,O7,O8,O69] ⊢ none-held 0/7",
  "accum_block_on_pendingContent #1 param:colon_fires_implicit_key.h_key := relay/built pos=[param:accum_block_on_pendingContent.h_key] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vpack := relay/built pos=[param:accum_block_on_pendingContent.h_vpack] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ some-held 20/41",
  "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_pendingContent.h_key := relay/built pos=[ctor:pendingContent.h_key] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_block_pending #1 param:accum_block_on_pendingContent.h_vpack := relay/built pos=[ctor:pendingContent.h_vpack] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ some-held 20/41",
  "accum_block_pending #1 param:colon_fires_props_key.h_key := relay/built pos=[ctor:pendingProps.h_key] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/36",
  "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslot := relay/built pos=[ctor:pendingBlockContent.h_kslot] origins=[O69] ⊢ none-held 0/1",
  "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_key := relay/built pos=[ctor:pendingBlockContent.h_key] origins=[O1,O2,O3,O6,O7,O8,O69] ⊢ none-held 0/7",
  "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslotUp := relay/built pos=[ctor:pendingBlockContent.h_kslotUp] origins=[O69] ⊢ none-held 0/1",
  "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslot := relay/built pos=[ctor:pendingBlock.h_kslot] origins=[O69] ⊢ none-held 0/1",
  "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslotUp := relay/built pos=[ctor:pendingBlock.h_kslotUp] origins=[O69] ⊢ none-held 0/1",
  "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vpack := paid:chain/built pos=[ctor:pendingMapValue.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/35",
  "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vpack := via/built pos=[ctor:pendingMapValue.h_kslot,ctor:pendingMapValue.h_explUp] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 18/36",
  "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vslot := paid:chain/built pos=[ctor:pendingMapValue.h_explUp] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key := via/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O1,O2,O3,O69] ⊢ none-held 0/4",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslotUp := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslotUp_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_nodeV := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_compact := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_ivl := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_key := via/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O4,O5,O69] none=[fact] ⊢ none-held 0/3",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslot := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslotE := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
  "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslotUp := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslotUp_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key := via/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O6,O7,O8,O69] ⊢ none-held 0/4",
  "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslotUp := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslotUp_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_nodeV := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_compact := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_ivl := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt,stamp,fact] ⊢ some-held 17/35",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_vpack := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 18/36",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_nodeV := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O17,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/36",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_compact := relay/built pos=[] origins=[O18] none=[punt] ⊢ all-held 1/1",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_ivl := relay/built pos=[] origins=[O19] none=[stamp,punt] ⊢ all-held 1/1",
  "accum_content_on_pendingMapValue_indented #1 param:explFrameValueLine.h_kslot := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt,fact,stamp] ⊢ some-held 17/35",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslot := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/36",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslotE := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O27,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/36",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact := relay/built pos=[] origins=[O28] none=[punt] ⊢ all-held 1/1",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl := relay/built pos=[] origins=[O29] none=[stamp,punt] ⊢ all-held 1/1",
  "accum_content_on_pendingMapValue_indented #2 param:explFrameValueLine.h_kslot := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_content_on_pendingMapValue_indented #3 param:explFrameValueLine.h_kslot := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
  "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_vpack := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O30,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 18/36",
  "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt,stamp,fact] ⊢ some-held 17/35",
  "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_vpack := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O38,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 18/36",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_nodeV := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O39,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/36",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_compact := relay/built pos=[] origins=[O40] none=[punt] ⊢ all-held 1/1",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_ivl := relay/built pos=[] origins=[O41] none=[stamp,punt] ⊢ all-held 1/1",
  "accum_content_on_pendingMapValue_indented #4 param:explFrameValueLine.h_kslot := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_content_pending #1 ctor:pendingProps.h_key := alt/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
  "accum_content_pending #1 ctor:pendingProps.h_kslot := relay/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/36",
  "accum_content_pending #1 ctor:pendingProps.h_kslotE := relay/built pos=[ctor:pendingProps.h_kslotE] origins=[O69] ⊢ none-held 0/1",
  "accum_content_pending #2 ctor:pendingProps.h_key := alt/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
  "accum_content_pending #2 ctor:pendingProps.h_kslot := relay/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/36",
  "accum_content_pending #2 ctor:pendingProps.h_kslotE := relay/built pos=[ctor:pendingProps.h_kslotE] origins=[O69] ⊢ none-held 0/1",
  "accum_content_pending #1 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
  "accum_content_pending #1 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/36",
  "accum_content_pending #2 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
  "accum_content_pending #2 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/36",
  "accum_content_pending #1 ctor:pendingBlockContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
  "accum_content_pending #1 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[ctor:pendingProps.h_kslotE] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_pending #1 ctor:pendingBlockContent.h_kslotUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_content_pending #3 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
  "accum_content_pending #3 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/36",
  "accum_content_pending #2 ctor:pendingBlockContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
  "accum_content_pending #2 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[ctor:pendingProps.h_kslotE] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_pending #2 ctor:pendingBlockContent.h_kslotUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_content_pending #4 ctor:pendingContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
  "accum_content_pending #4 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/36",
  "accum_content_pending #3 ctor:pendingBlockContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
  "accum_content_pending #3 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[ctor:pendingProps.h_kslotE] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_content_pending #3 ctor:pendingBlockContent.h_kslotUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_content_pending #5 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
  "accum_content_pending #5 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/36",
  "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslot_old := relay/built pos=[ctor:pendingBlock.h_kslot] origins=[O69] ⊢ none-held 0/1",
  "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslotUp_old := relay/built pos=[ctor:pendingBlock.h_kslotUp] origins=[O69] ⊢ none-held 0/1",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_vslot := step/built pos=[ctor:pendingMapValue.h_vslot] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O53,O54,O55,O62,O63,O64,O65,O66,O67,O68,O69] ⊢ some-held 27/49",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_kslot := relay/built pos=[ctor:pendingMapValue.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_ivl_mv := relay/built pos=[ctor:pendingMapValue.h_ivl] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O52,O54,O55,O56,O57,O58,O59,O60,O61,O68,O69] ⊢ some-held 27/49",
  "accum_flow_open_depth0 #1 param:flowKeyRoute_of_open.h_compact_pair := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "accum_flow_open_depth0 #2 param:flowKeyRoute_of_open.h_compact_pair := paid:chain/built pos=[ctor:pendingBlock.h_kslot] origins=[O69] none=[punt] ⊢ none-held 0/1",
  "accum_flow_open_depth0 #3 param:flowKeyRoute_of_open.h_compact_pair := paid:route/built pos=[] origins=[O42] none=[punt] ⊢ all-held 1/1",
  "accum_step_flow #1 ctor:pendingContent.h_key := via/built pos=[] origins=[O43] ⊢ none-held 0/1",
  "accum_step_flow #1 ctor:pendingContent.h_vpack := via/built pos=[] origins=[O44] ⊢ none-held 0/1",
  "accum_step_flow #1 param:flowKeyPack_of_close.h_key := relay/built pos=[] origins=[O45] ⊢ none-held 0/1",
  "accum_step_flow #1 param:flowVPack_of_close.h_vslot := relay/built pos=[] origins=[O46] ⊢ none-held 0/1",
  "accum_step_flow #2 ctor:pendingContent.h_key := via/built pos=[] origins=[O47] ⊢ none-held 0/1",
  "accum_step_flow #2 ctor:pendingContent.h_vpack := via/built pos=[] origins=[O48] ⊢ none-held 0/1",
  "accum_step_flow #2 param:flowKeyPack_of_close.h_key := relay/built pos=[] origins=[O49] ⊢ none-held 0/1",
  "accum_step_flow #2 param:flowVPack_of_close.h_vslot := relay/built pos=[] origins=[O50] ⊢ none-held 0/1",
  "colon_fires_implicit_key #1 param:colon_open_map_implicit.h_kslot := relay/built pos=[param:colon_fires_implicit_key.h_key] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "colon_fires_props_key #1 param:colon_open_map_props.h_kslot := relay/built pos=[param:colon_fires_props_key.h_key] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ some-held 17/35",
  "colon_open_map #1 ctor:pendingMapValue.h_ivl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_kslot := paid:frames/built pos=[] origins=[O51] none=[punt] ⊢ none-held 0/1",
  "colon_open_map #1 ctor:pendingMapValue.h_explUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_ivl := paid:chain/built pos=[param:colon_open_map_explicit.hvp] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ some-held 21/42",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_vslot := paid:chain/built pos=[param:colon_open_map_explicit.hvp] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ some-held 21/42",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_kslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_explUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_ivl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_kslot := paid:chain/built pos=[param:colon_open_map_implicit.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/35",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_explUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_ivl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_vslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_kslot := paid:chain/built pos=[param:colon_open_map_props.h_kslot] origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] none=[punt] ⊢ some-held 17/35",
  "colon_open_map_props #1 ctor:pendingMapValue.h_explUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "compact_open_map #1 ctor:pendingMapValue.h_ivl := relay/built pos=[] origins=[O52] none=[stamp,fact] ⊢ none-held 0/1",
  "compact_open_map #1 ctor:pendingMapValue.h_vslot := relay/built pos=[] origins=[O53] none=[punt,fact] ⊢ none-held 0/1",
  "compact_open_map #1 ctor:pendingMapValue.h_kslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "compact_open_map #1 ctor:pendingMapValue.h_explUp := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingProps.h_key := relay/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
  "content_dispatch_routed #1 ctor:pendingProps.h_kslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingProps.h_kslotE := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingProps.h_key := relay/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
  "content_dispatch_routed #2 ctor:pendingProps.h_kslot := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingProps.h_kslotE := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingContent.h_key := relay/built pos=[] origins=[O54] none=[punt,stamp] ⊢ none-held 0/1",
  "content_dispatch_routed #1 ctor:pendingContent.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingContent.h_key := relay/built pos=[] origins=[O55] none=[punt,stamp] ⊢ none-held 0/1",
  "content_dispatch_routed #2 ctor:pendingContent.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
  "indicator_open_map #1 param:question_open_map.h_explUp_chain := relay/built pos=[param:indicator_open_map.h_explUp_chain] origins=[O69] ⊢ none-held 0/1",
  "question_open_map #1 ctor:pendingMapValue.h_ivl := paid:route/built pos=[] origins=[O56,O57,O58,O59,O60,O61] ⊢ all-held 6/6",
  "question_open_map #1 ctor:pendingMapValue.h_vslot := paid:route/built pos=[] origins=[O62,O63,O64,O65,O66,O67] ⊢ all-held 6/6",
  "question_open_map #1 ctor:pendingMapValue.h_kslot := paid:chain/built pos=[param:question_open_map.h_explUp_chain] origins=[O68,O69] none=[punt] ⊢ none-held 0/2",
  "question_open_map #1 ctor:pendingMapValue.h_explUp := paid:chain/built pos=[param:question_open_map.h_explUp_chain] origins=[O69] none=[punt] ⊢ none-held 0/1"]
def expectedPerPos : List String := [
  "ctor:pendingContent.h_key packaged writers=12 punt=0 stamp=0 built=12 unborn=0 dead=0 allHeld=0 someHeld=2 noneHeld=4 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "ctor:pendingContent.h_vpack writers=12 punt=2 stamp=0 built=10 unborn=0 dead=0 allHeld=0 someHeld=8 noneHeld=2 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ 20/41 held",
  "ctor:pendingProps.h_key packaged writers=6 punt=0 stamp=0 built=6 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=1 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "ctor:pendingProps.h_kslot writers=6 punt=2 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=3 noneHeld=1 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O26,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/36 held",
  "ctor:pendingProps.h_kslotE writers=6 punt=3 stamp=0 built=3 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=3 origins=[O69] ⊢ 0/1 held",
  "ctor:pendingBlockContent.h_key packaged writers=6 punt=0 stamp=0 built=6 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O1,O2,O3,O6,O7,O8,O69] ⊢ 0/7 held",
  "ctor:pendingBlockContent.h_kslot writers=6 punt=0 stamp=0 built=6 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=6 origins=[O69] ⊢ 0/1 held",
  "ctor:pendingBlockContent.h_kslotUp writers=6 punt=3 stamp=0 built=3 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=3 origins=[O69] ⊢ 0/1 held",
  "ctor:pendingBlock.h_kslot writers=7 punt=1 stamp=0 built=6 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=6 origins=[O69] ⊢ 0/1 held",
  "ctor:pendingBlock.h_kslotUp writers=7 punt=1 stamp=0 built=6 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=6 origins=[O69] ⊢ 0/1 held",
  "ctor:pendingMapValue.h_ivl writers=6 punt=0 stamp=3 built=3 unborn=0 dead=0 allHeld=1 someHeld=1 noneHeld=1 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O52,O54,O55,O56,O57,O58,O59,O60,O61,O68,O69] ⊢ 27/49 held",
  "ctor:pendingMapValue.h_vslot writers=6 punt=3 stamp=0 built=3 unborn=0 dead=0 allHeld=1 someHeld=1 noneHeld=1 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O53,O54,O55,O62,O63,O64,O65,O66,O67,O68,O69] ⊢ 27/49 held",
  "ctor:pendingMapValue.h_kslot writers=6 punt=2 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=2 noneHeld=2 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "ctor:pendingMapValue.h_explUp writers=6 punt=5 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_block_on_closeThenBlock.h_vpack writers=11 punt=7 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=4 noneHeld=0 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ 21/42 held",
  "param:accum_block_on_closeThenBlock.h_vslot writers=11 punt=10 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_block_on_pendingBlock.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_block_on_pendingBlock.h_kslotUp writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_block_on_pendingBlockContent.h_key packaged writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O1,O2,O3,O6,O7,O8,O69] ⊢ 0/7 held",
  "param:accum_block_on_pendingBlockContent.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_block_on_pendingBlockContent.h_kslotUp writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_block_on_pendingContent.h_key packaged writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "param:accum_block_on_pendingContent.h_vpack writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ 20/41 held",
  "param:accum_content_on_pendingBlock_indented.h_kslotUp_old writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_content_on_pendingBlock_indented.h_kslot_old writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:accum_content_on_pendingMapValue_indented.h_ivl_mv writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O52,O54,O55,O56,O57,O58,O59,O60,O61,O68,O69] ⊢ 27/49 held",
  "param:accum_content_on_pendingMapValue_indented.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "param:accum_content_on_pendingMapValue_indented.h_vslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O53,O54,O55,O62,O63,O64,O65,O66,O67,O68,O69] ⊢ 27/49 held",
  "param:colon_fires_implicit_key.h_key packaged writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=1 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "param:colon_fires_props_key.h_key packaged writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "param:colon_open_map_explicit.hvp writers=3 punt=0 stamp=0 built=3 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=2 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O20,O21,O22,O23,O24,O25,O26,O30,O31,O32,O33,O34,O35,O36,O37,O38,O43,O44,O47,O48,O51,O54,O55,O68,O69] ⊢ 21/42 held",
  "param:colon_open_map_implicit.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "param:colon_open_map_props.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "param:entryChainMap.up writers=3 punt=0 stamp=0 built=3 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=3 origins=[O69] ⊢ 0/1 held",
  "param:entryKeyPack_of_dispatch.h_compact writers=4 punt=0 stamp=0 built=4 unborn=0 dead=0 allHeld=2 someHeld=0 noneHeld=2 origins=[O18,O40,O69] ⊢ 2/3 held",
  "param:entryKeyPack_of_dispatch.h_ivl writers=4 punt=0 stamp=0 built=4 unborn=0 dead=0 allHeld=2 someHeld=0 noneHeld=2 origins=[O19,O41,O69] ⊢ 2/3 held",
  "param:entryKeyPack_of_dispatch.h_nodeV writers=4 punt=0 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=2 noneHeld=2 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O17,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O39,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/37 held",
  "param:entryPropsKeyPack_of_dispatch.h_compact writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=1 someHeld=0 noneHeld=1 origins=[O28,O69] ⊢ 1/2 held",
  "param:entryPropsKeyPack_of_dispatch.h_ivl writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=1 someHeld=0 noneHeld=1 origins=[O29,O69] ⊢ 1/2 held",
  "param:entryPropsKeyPack_of_dispatch.h_nodeV writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=1 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O27,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/36 held",
  "param:explFrameValueLine.h_kslot writers=4 punt=0 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=4 noneHeld=0 origins=[O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O20,O21,O22,O23,O24,O25,O31,O32,O33,O34,O35,O36,O37,O43,O47,O51,O54,O55,O68,O69] ⊢ 17/35 held",
  "param:flowKeyPack_of_close.h_key writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O45,O49] ⊢ 0/2 held",
  "param:flowKeyRoute_of_open.h_compact_pair writers=3 punt=1 stamp=0 built=2 unborn=0 dead=0 allHeld=1 someHeld=0 noneHeld=1 origins=[O42,O69] ⊢ 1/2 held",
  "param:flowVPack_of_close.h_vslot writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O46,O50] ⊢ 0/2 held",
  "param:indicator_open_map.h_explUp_chain writers=4 punt=2 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O69] ⊢ 0/1 held",
  "param:question_open_map.h_explUp_chain writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O69] ⊢ 0/1 held",
  "param:slotChainMap.up writers=3 punt=0 stamp=0 built=3 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=3 origins=[O69] ⊢ 0/1 held"]
def expectedUnborn : List String := []
def expectedLine : String :=
  "positions=47 packaged=7 packConsts=[ImplicitKeyPack,PropsKeyPack] rows=180 ctorRows=98 paramRows=82 packagedRows=29 punt=42 stamp=3 built=135 origins=70 originRows=38 route=23 frames=24 tail=0 other=7 concl=8 invariant=8 heldOrigins=40 allHeld=9 someHeld=39 noneHeld=73 unbornRows=0 relayedPunt=0 relayedStamp=10 relayedAbsurd=4 relayedFact=0 deadRows=0 unbornPos=0 rounds=4 follows=309 lets=549 lapps=645 alts=4309 nodes=12292 liteNodes=490876"

/-! ## §4 The reading -/

structure Origin where
  row : Nat
  kind : String
  label : String
  lvl : Option String
  deriving Inhabited

def dedupNat (xs : Array Nat) : Array Nat := (xs.qsort (· < ·)).foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let pe := mkPackEnv env
  let cs ← collect pe
  let posKeys : Std.HashSet String := cs.positions.foldl (fun s p => s.insert p.key) {}
  let posMap : Std.HashMap String Position := cs.positions.foldl (fun m p => m.insert p.key p) {}
  let w ← IO.mkRef ({} : W)
  for n in sorted cs.thms do walkTheoremP w cs.cd n
  let ws ← w.get
  let rowKey (r : WRow) : String := s!"{r.kind}:{r.target}"
  let letsBy : Std.HashMap Name (Array LetRec) := ws.lets.foldl (fun m l => m.insert l.lem ((m.getD l.lem #[]).push l)) {}
  let lappsBy : Std.HashMap Name (Array LApp) := ws.lapps.foldl (fun m a => m.insert a.lem ((m.getD a.lem #[]).push a)) {}
  let altsBy : Std.HashMap Name (Array AltRec) := ws.alts.foldl (fun m a => m.insert a.lem ((m.getD a.lem #[]).push a)) {}
  let memo : BMemo ← IO.mkRef {}
  let budget : Budget ← IO.mkRef 0
  let dyn : DynAlts ← IO.mkRef #[]
  let fmemo : FMemo ← IO.mkRef {}
  -- every row: its class (item 261's reading), its bottoms and where they lead
  let mut srcs : Array (Array Src) := #[]
  let mut myCls : Array String := #[]
  let mut prs : Array PackRead := #[]
  let mut owns : Array String := #[]
  let mut follows := 0
  for r in ws.rows do
    unless r.argIdx < r.args.size do throwError "{r.target}: {r.args.size} args"
    let some pos := posMap[rowKey r]? | throwError "{rowKey r}: no position"
    budget.set 100000
    dyn.set #[]
    let mut own := "—"
    if r.kind == "ctor" then
      let some (.ctorInfo cv) := env.find? r.callee | throwError "{r.callee}"
      let mut ty := cv.type
      let mut j := 0
      while own == "—" do
        match ty with
        | .forallE _ t b _ =>
          if j ≥ cv.numParams && t.consumeMData.isConstOf ``Nat && j < r.args.size then own := ppc r.st r.args[j]!
          ty := b; j := j + 1
        | _ => break
    owns := owns.push own
    prs := prs.push (← packCls env r.st r.args[r.argIdx]! r.vcLeft r.otherTrue)
    let bots ← bottomsOf pe memo budget dyn r.st r.args[r.argIdx]! pos.path
    let cx : FCx := { pe, memo, budget, dyn, fmemo, lem := r.lem, posKeys, lets := letsBy.getD r.lem #[], lapps := lappsBy.getD r.lem #[], alts := altsBy.getD r.lem #[] }
    let mut ss : Array Src := #[]
    for bt in bots do
      follows := follows + 1
      ss := ss ++ (← followBot cx bt)
    srcs := srcs.push (dedupSrc ss)
    let terms := bots.filterMap fun | .term t => some t | _ => none
    myCls := myCls.push (if bots.size > 0 && terms.size == bots.size && terms.all (· == "punt") then "punt"
      else if bots.size > 0 && terms.size == bots.size && terms.all (fun t => t == "punt" || t == "stamp") then "stamp" else "built")
  -- the origins, each once per (row, label)
  let mut origins : Array Origin := #[]
  let mut originIdx : Std.HashMap String Nat := {}
  let mut rowOr : Array (Array Nat) := #[]
  let mut rowPos : Array (Array String) := #[]
  let mut rowDead : Array (Array String) := #[]
  let mut rowNone : Array (Array String) := #[]
  for i in [0:ws.rows.size] do
    let mut os : Array Nat := #[]
    let mut ps : Array String := #[]
    let mut ds : Array String := #[]
    let mut ns : Array String := #[]
    for s in srcs[i]! do
      match s with
      | .origin kind label lvl =>
        let k := s!"{i}|{label}"
        let idx ← match originIdx[k]? with
          | some idx => pure idx
          | none =>
            let idx := origins.size
            origins := origins.push { row := i, kind, label, lvl }
            originIdx := originIdx.insert k idx
            pure idx
        os := os.push idx
      | .pos key => unless ps.contains key do ps := ps.push key
      | .dead why => unless ds.contains why do ds := ds.push why
      | .none why => unless ns.contains why do ns := ns.push why
    rowOr := rowOr.push (dedupNat os); rowPos := rowPos.push ps; rowDead := rowDead.push ds; rowNone := rowNone.push ns
  -- the least fixpoint over the producer relation
  let mut byKey : Std.HashMap String (Array Nat) := {}
  for i in [0:ws.rows.size] do
    let k := rowKey ws.rows[i]!
    byKey := byKey.insert k ((byKey.getD k #[]).push i)
  let mut posOr : Std.HashMap String (Array Nat) := {}
  let mut rounds := 0
  let mut changed := true
  while changed && rounds < 64 do
    changed := false
    rounds := rounds + 1
    for p in cs.positions do
      let mut acc : Array Nat := #[]
      for i in byKey.getD p.key #[] do
        acc := acc ++ rowOr[i]!
        for q in rowPos[i]! do acc := acc ++ posOr.getD q #[]
      let acc2 := dedupNat acc
      if acc2 != posOr.getD p.key #[] then
        posOr := posOr.insert p.key acc2
        changed := true
  -- the tail at each origin: item 261's reading at the origin row, and the
  -- route's own level for a route
  let mut originLines : Array String := #[]
  let mut originHeld : Array Bool := #[]
  for o in origins, oi in [0:origins.size] do
    let r := ws.rows[o.row]!
    let holds := holdsOf env r.st
    let (atoms, var) := atomsOf prs[o.row]!.wits owns[o.row]!
    let hs := hits holds atoms var
    let v1 := if !hs.isEmpty then s!"held({String.intercalate "," hs.toList})" else if atoms.isEmpty then "level-var" else "none"
    -- the strict reading: a level the pack names (never a list variable's
    -- equality with a face's own list, which a frames-built pack has by
    -- construction)
    let hsS := hits holds atoms none
    let h2 : Array String := match o.lvl with | some l => hits holds [l] none | none => #[]
    let v2 : Option String := match o.lvl with
      | some l => some (if h2.isEmpty then s!"@{l}:none" else s!"@{l}:held({String.intercalate "," h2.toList})")
      | none => none
    let held := if o.kind == "route" && o.lvl.isSome then !h2.isEmpty else !hsS.isEmpty
    originHeld := originHeld.push held
    originLines := originLines.push s!"  O{oi} {short r.lem} #{r.occ} {rowKey r} ← {o.kind}({o.label}) lvl={o.lvl.getD "—"} ⊢ {v1}{match v2 with | some s => s!" | {s}" | none => ""} → {if held then "held" else "unheld"}"
  -- every row's resolution
  let mut rowLines : Array String := #[]
  let mut cnt : Std.HashMap String Nat := {}
  let bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat := m.insert k (m.getD k 0 + 1)
  let mut perRows : Std.HashMap String (Array String) := {}
  for i in [0:ws.rows.size] do
    let r := ws.rows[i]!
    let pr := prs[i]!
    let clsHead := ((pr.cls.splitOn "(")[0]?).getD pr.cls
    let clsTag := if clsHead.startsWith "paid:" then clsHead
      else if clsHead.startsWith "via:" then "via" else if clsHead.startsWith "alt[" then "alt"
      else if clsHead.startsWith "relay:" then "relay" else if clsHead.startsWith "step" then "step"
      else if clsHead.startsWith "other" then "other" else clsHead
    let mut os0 := rowOr[i]!
    for q in rowPos[i]! do os0 := os0 ++ posOr.getD q #[]
    let os := dedupNat os0
    let nh := (os.filter fun oi => originHeld[oi]!).size
    let verdict :=
      if myCls[i]! != "built" then "—"
      else if os.isEmpty then
        if !rowDead[i]!.isEmpty then "dead"
        else if !rowPos[i]!.isEmpty then "unborn"
        else if rowNone[i]!.contains "stamp" then "stamp*"
        else if rowNone[i]!.contains "punt" then "punt*"
        else if rowNone[i]!.contains "absurd" then "absurd*"
        else if rowNone[i]!.contains "fact" then "fact*"
        else "unborn"
      else if nh == os.size then s!"all-held {nh}/{os.size}"
      else if nh == 0 then s!"none-held 0/{os.size}"
      else s!"some-held {nh}/{os.size}"
    let vTag := ((verdict.splitOn " ")[0]?).getD verdict
    cnt := bump cnt clsTag
    cnt := bump cnt s!"b:{myCls[i]!}"
    cnt := bump cnt s!"v:{vTag}"
    cnt := bump cnt s!"k:{r.kind}"
    let key := rowKey r
    if (posMap[key]!).packaged then cnt := bump cnt "packagedRows"
    perRows := perRows.insert key ((perRows.getD key #[]).push s!"{myCls[i]!} {vTag}")
    rowLines := rowLines.push s!"  {short r.lem} #{r.occ} {key} := {clsTag}/{myCls[i]!} pos=[{String.intercalate "," rowPos[i]!.toList}] origins=[{String.intercalate "," (os.map fun o => s!"O{o}").toList}]{if rowDead[i]!.isEmpty then "" else s!" dead=[{String.intercalate "," rowDead[i]!.toList}]"}{if rowNone[i]!.isEmpty then "" else s!" none=[{String.intercalate "," rowNone[i]!.toList}]"} ⊢ {verdict}"
  -- per position
  let mut perLines : Array String := #[]
  let mut unbornLines : Array String := #[]
  for p in cs.positions do
    let xs := perRows.getD p.key #[]
    let c (s : String) := (xs.filter fun x => (x.splitOn " ")[0]! == s).size
    let v (s : String) := (xs.filter fun x => (x.splitOn " ")[1]! == s).size
    let os := posOr.getD p.key #[]
    let nh := (os.filter fun oi => originHeld[oi]!).size
    let touched := xs.size - c "punt" - c "stamp"
    let verdict := if touched == 0 then "punt-only" else if os.isEmpty then (if v "dead" > 0 then "dead" else if v "unborn" > 0 then "unborn" else "relayed-punts") else s!"{nh}/{os.size} held"
    perLines := perLines.push s!"  {p.key}{if p.packaged then " packaged" else ""} writers={xs.size} punt={c "punt"} stamp={c "stamp"} built={c "built"} unborn={v "unborn"} dead={v "dead"} allHeld={v "all-held"} someHeld={v "some-held"} noneHeld={v "none-held"} origins=[{String.intercalate "," (os.map fun o => s!"O{o}").toList}] ⊢ {verdict}"
    if verdict == "unborn" then unbornLines := unbornLines.push s!"  {p.key} writers={xs.size} punt={c "punt"}"
  let g (k : String) := cnt.getD k 0
  let originRows := (dedupNat (origins.map (·.row))).size
  let okind (k : String) := (origins.filter fun o => o.kind == k).size
  let heldO := (originHeld.filter id).size
  let packL := ((pe.packConsts.toArray.map short).qsort (· < ·)).toList
  let line := s!"positions={cs.positions.size} packaged={(cs.positions.filter (·.packaged)).size} packConsts=[{String.intercalate "," packL}] rows={ws.rows.size} ctorRows={g "k:ctor"} paramRows={g "k:param"} packagedRows={g "packagedRows"} punt={g "b:punt"} stamp={g "b:stamp"} built={g "b:built"} origins={origins.size} originRows={originRows} route={okind "route"} frames={okind "frames"} tail={okind "tail"} other={okind "other"} concl={okind "concl"} invariant={okind "invariant"} heldOrigins={heldO} allHeld={g "v:all-held"} someHeld={g "v:some-held"} noneHeld={g "v:none-held"} unbornRows={g "v:unborn"} relayedPunt={g "v:punt*"} relayedStamp={g "v:stamp*"} relayedAbsurd={g "v:absurd*"} relayedFact={g "v:fact*"} deadRows={g "v:dead"} unbornPos={unbornLines.size} rounds={rounds} follows={follows} lets={ws.lets.size} lapps={ws.lapps.size} alts={ws.alts.size} nodes={ws.nodes} liteNodes={ws.liteNodes}"
  logInfo s!"ValueLineOrigins {line}"
  logInfo s!"positions:\n{String.intercalate "\n" (cs.positions.map fun p => "  " ++ p.line).toList}"
  logInfo s!"origins:\n{String.intercalate "\n" originLines.toList}"
  logInfo s!"rows:\n{String.intercalate "\n" rowLines.toList}"
  logInfo s!"perPos:\n{String.intercalate "\n" perLines.toList}"
  logInfo s!"unborn:\n{String.intercalate "\n" unbornLines.toList}"
  unless (cs.positions.filter (!·.packaged)).size == 40 do throwError "item 261's positions moved under this pass: {(cs.positions.filter (!·.packaged)).size}"
  unless origins.size > 0 do throwError "no origin resolved"
  unless pinned do return
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedPositions" (cs.positions.map (·.line)) expectedPositions
  check "expectedOrigins" originLines expectedOrigins
  check "expectedRows" rowLines expectedRows
  check "expectedPerPos" perLines expectedPerPos
  check "expectedUnborn" unbornLines expectedUnborn
  unless line == expectedLine do
    throwError "ValueLineOrigins moved:\n  got      {line}\n  expected {expectedLine}"

end Tests.Guards.ValueLineOrigins
