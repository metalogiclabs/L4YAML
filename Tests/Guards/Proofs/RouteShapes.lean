/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ExitHandoff

/-!
# How many route shapes the hand-offs have (DOCS item 248)

Item 247 found that every `nil` exit of the second wave hands the content to
a park whose closures promise the stream past it, built from the absorbed
stream.  Threading the arm re-derives each such promise under an open entry,
so the price is one re-routing lemma per distinct SPINE the promises consume,
spent at the sites that build it — and item 247's recorded NEXT warned that a
census by the production's NAME would price it short: `SBlockIndented` under
`.blockIn` and under `.blockOut`, or at `n` and at `n + 1`, are two routes.

**§1 reads the parks' closures statically.**  Each field of the ten
`PendingNode` constructors (and of `FlowBaseRoutes`, the flow bases' routes)
is descended through `→`, `∀`, `∧`, `∨` and `∃`, unfolding one level of a
definition applied to `sp_start` (the key packs).  A CLOSURE is a
`∀`-telescope with at least one SPAN premise — an application whose last two
arguments are positions — and a conclusion from `sp_start`.  Its SPINE is the
Nat equations beside it, its ORIGIN (the first premise's start position), each
premise as `Head(non-position arguments)` with bound names normalized to `_`
and the park's own parameters kept, and the conclusion KIND — `Stream`, or a
resume kind that consumes more productions after the premises.  Three
groupings: by the first premise's HEAD (the failure mode), by origin and
first premise, by the whole spine.

**§2 reads what the forty-three exits build.**  Item 247's walk, with the
park TERM kept: at each `nil` exit whose park is a constructor application,
each closure of that constructor is located by its field index and its
path through the disjunctions, and the argument classified — REAL (a lambda,
a lemma, the closure's side of the disjunction), PUNT (the other side), FWD
(a hypothesis or an obtained variable passed along), OPAQUE (a lemma yields
the whole disjunction).  The k is the number of distinct spines with at
least one real site.

**§3 reads what closed the park** at the exits whose stream was built inside
the proof: the type of the hypothesis applied, as a spine, against §1.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropDependents (sorted)
open Tests.Guards.ExitHandoff (five shortPark headOf tally)

set_option autoImplicit false

namespace Tests.Guards.RouteShapes

/-! ## §1 The closures, statically -/

/-- One closure a park or a flow base carries. -/
structure Closure where
  owner : String
  field : String
  /-- The field's index among the constructor's arguments. -/
  fieldIdx : Nat
  /-- How to reach the telescope from the field: `L`/`R` a disjunct, `1`…
      a conjunct, `E` an existential's body, `λ` a premise before a
      connective. -/
  path : List String
  optional : Bool
  guarded : Bool
  packed : Bool
  /-- Nat equations beside the closure, names normalized. -/
  constraints : String
  /-- Each span premise as `Head(non-position arguments)`, every variable
      `_`, arithmetic kept: `SBlockNode(_+1,blockIn)`. -/
  premises : Array String
  /-- The conclusion's kind. -/
  concl : String
  /-- The same, with the owner's own names: for reading. -/
  label : String
  deriving Inhabited, Repr

def short (n : Name) : String := n.components.getLast!.toString

def Closure.head (c : Closure) : String :=
  ((c.premises[0]?.getD "?").splitOn "(")[0]!
def Closure.first (c : Closure) : String := c.premises[0]?.getD "?"
/-- The shape: constraints, premises, conclusion — no names. -/
def Closure.spine (c : Closure) : String :=
  s!"{c.constraints}{String.intercalate " > " c.premises.toList} ⇒ {c.concl}"
def Closure.flags (c : Closure) : String :=
  (if c.optional then "opt" else "req") ++ (if c.guarded then "+guard" else "") ++
  (if c.packed then "+pack" else "")

def natOf? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal k) => some k
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match (e.getArg! 1).consumeMData with
      | .lit (.natVal k) => some k
      | _ => none
    else none

/-- Render an argument.  Named: the owner's parameters by name and bound
    variables as `_`.  Normalized (`params = #[]`): every variable `_`.
    Arithmetic and lists are spelled out, other applications by head and
    explicit arguments. -/
partial def ren (params : Array Expr) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if let some k := natOf? e then return toString k
  match e with
  | .fvar id =>
    if params.contains e then return (← id.getDecl).userName.toString else return "_"
  | .const n _ => return short n
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if e.isAppOfArity ``HAdd.hAdd 6 then return s!"{← ren params args[4]!}+{← ren params args[5]!}"
    if e.isAppOfArity ``HSub.hSub 6 then return s!"{← ren params args[4]!}-{← ren params args[5]!}"
    if e.isAppOfArity ``Char.ofNat 1 then
      if let some k := natOf? args[0]! then return s!"'{Char.ofNat k}'"
    if e.isAppOfArity ``List.cons 3 then return s!"{← ren params args[1]!}::{← ren params args[2]!}"
    if e.isAppOfArity ``List.nil 1 then return "[]"
    if e.isAppOfArity ``Eq 3 then return s!"{← ren params args[1]!}={← ren params args[2]!}"
    match f with
    | .const n _ =>
      let info ← getFunInfoNArgs f args.size
      let mut parts : Array String := #[]
      for i in [:args.size] do
        let explicit := if h : i < info.paramInfo.size then info.paramInfo[i].isExplicit else true
        if explicit then parts := parts.push (← ren params args[i]!)
      return s!"{short n}({String.intercalate "," parts.toList})"
    | .fvar _ =>
      return s!"{← ren params f}({String.intercalate "," (← args.toList.mapM (ren params))})"
    | _ => return "?"
  | .lam .. => return "λ"
  | .forallE .. => return "∀"
  | _ => return e.ctorName

def isSurfPos (t : Expr) : Bool := t.consumeMData.isConstOf ``SurfPos

/-- A span: an application whose last two arguments are positions. -/
def spanOf? (t : Expr) : MetaM (Option (Expr × Array Expr × Expr × Expr)) := do
  let t := t.consumeMData
  let args := t.getAppArgs
  if args.size < 2 then return none
  let a := args[args.size - 2]!
  let b := args[args.size - 1]!
  if isSurfPos (← inferType a) && isSurfPos (← inferType b) then
    return some (t.getAppFn, args.extract 0 (args.size - 2), a, b)
  return none

/-- `Head(explicit non-position arguments)`. -/
def renSpan (params : Array Expr) (f : Expr) (pre : Array Expr) : MetaM String := do
  match f with
  | .const n _ =>
    let info ← getFunInfoNArgs f (pre.size + 2)
    let mut parts : Array String := #[]
    for i in [:pre.size] do
      let explicit := if h : i < info.paramInfo.size then info.paramInfo[i].isExplicit else true
      if explicit then parts := parts.push (← ren params pre[i]!)
    return if parts.isEmpty then short n else s!"{short n}({String.intercalate "," parts.toList})"
  | _ => ren params f

/-- The conclusion's kind. -/
partial def renConcl (params : Array Expr) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if e.isAppOfArity ``SLYamlStream 2 || e.isAppOfArity ``SLYamlStream 1 then return "Stream"
  if e.isAppOfArity ``ResumeFrames 3 then
    return s!"Resume({← ren params (e.getArg! 1)})▹{← renConcl params (e.getArg! 0)}"
  if e.isAppOf ``ExplValueLine then return s!"ExplValueLine({← ren params (e.getArg! 1)})"
  if e.isAppOf ``SeqEntryTail then return s!"SeqEntryTail({← ren params (e.getArg! 1)})"
  match ← spanOf? e with
  | some (f, pre, _, _) => renSpan params f pre
  | none => ren params e

structure Ctx where
  owner : String
  field : String
  fieldIdx : Nat
  params : Array Expr
  spStart : FVarId

structure Found where
  closures : Array Closure := #[]
  /-- Conclusions from `sp_start` with no span premise. -/
  facts : Array String := #[]
  /-- Closures whose conclusion is not from `sp_start`. -/
  others : Array String := #[]

def isNatEq (t : Expr) : Bool :=
  t.isAppOfArity ``Eq 3 && (t.getArg! 0).consumeMData.isConstOf ``Nat

def isConnective (e : Expr) : Bool :=
  e.isAppOfArity ``Or 2 || e.isAppOfArity ``And 2 || e.isAppOfArity ``Exists 2

/-- Unfold a definition applied to `sp_start` when it opens onto connectives
    or a telescope: a pack.  `ExplValueLine` and `SeqEntryTail` are conclusion
    kinds and stay folded. -/
def unfoldPack? (e : Expr) : MetaM (Option Expr) := do
  match e.getAppFn with
  | .const n _ =>
    if n == ``ExplValueLine || n == ``SeqEntryTail then return none
    match (← getEnv).find? n with
    | some (.defnInfo _) =>
      match ← unfoldDefinition? e with
      | some u =>
        let u := u.consumeMData
        if isConnective u || u.isForall then return some u else return none
      | none => return none
    | _ => return none
  | _ => return none

partial def descend (cx : Ctx) (e : Expr) (path : List String) (opt guard packed : Bool)
    (cons consL : Array String) (acc : IO.Ref Found) : MetaM Unit := do
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    let mut conj : Array Expr := #[]
    let mut cur := e
    while cur.isAppOfArity ``And 2 do
      conj := conj.push (cur.getArg! 0).consumeMData
      cur := (cur.getArg! 1).consumeMData
    conj := conj.push cur
    let mut cons := cons
    let mut consL := consL
    for c in conj do
      if isNatEq c then
        cons := cons.push (← ren #[] c)
        consL := consL.push (← ren cx.params c)
    for i in [:conj.size] do
      let c := conj[i]!
      unless isNatEq c do
        descend cx c (path ++ [toString (i + 1)]) opt guard packed cons consL acc
    return
  if e.isAppOfArity ``Or 2 then
    let a := (e.getArg! 0).consumeMData
    let b := (e.getArg! 1).consumeMData
    if b.isConstOf ``True then descend cx a (path ++ ["L"]) true guard packed cons consL acc
    else if a.isConstOf ``True then descend cx b (path ++ ["R"]) true guard packed cons consL acc
    else
      descend cx a (path ++ ["L"]) opt guard packed cons consL acc
      descend cx b (path ++ ["R"]) opt guard packed cons consL acc
    return
  if e.isAppOfArity ``Exists 2 then
    match (e.getArg! 1).consumeMData with
    | .lam x t b bi =>
      withLocalDecl x bi t fun fv =>
        descend cx (b.instantiate1 fv) (path ++ ["E"]) opt guard packed cons consL acc
    | _ => pure ()
    return
  if e.isForall then
    forallTelescope e fun xs body => do
      let mut spans : Array String := #[]
      let mut spansL : Array String := #[]
      let mut origin := ""
      let mut guard := guard
      let mut cons := cons
      let mut consL := consL
      for x in xs do
        let t := (← inferType x).consumeMData
        if !(← isProp t) then continue
        match ← spanOf? t with
        | some (f, pre, a, _) =>
          if spans.isEmpty then origin ← ren cx.params a
          spans := spans.push (← renSpan #[] f pre)
          spansL := spansL.push (← renSpan cx.params f pre)
        | none =>
          if t.isAppOfArity ``Membership.mem 5 then continue
          if isNatEq t then
            cons := cons.push (← ren #[] t)
            consL := consL.push (← ren cx.params t)
          else guard := true
      let body := body.consumeMData
      let fromStart := body.containsFVar cx.spStart
      if isConnective body then
        -- the premises are lambdas in the term before the connective
        descend cx body (path ++ (List.replicate xs.size "λ")) opt guard packed cons consL acc
      else if fromStart && !spans.isEmpty then
        let cs := cons.qsort (· < ·)
        let csL := consL.qsort (· < ·)
        let consS := if cs.isEmpty then "" else s!"[{String.intercalate "; " cs.toList}] "
        let consSL := if csL.isEmpty then "" else s!"[{String.intercalate "; " csL.toList}] "
        let concl ← renConcl #[] body
        let conclL ← renConcl cx.params body
        let label := s!"{consSL}{origin}: {String.intercalate " > " spansL.toList} ⇒ {conclL}"
        let cl : Closure :=
          { owner := cx.owner, field := cx.field, fieldIdx := cx.fieldIdx, path, optional := opt,
            guarded := guard, packed, constraints := consS, premises := spans, concl, label }
        acc.modify fun f => { f with closures := f.closures.push cl }
      else if fromStart then
        match ← unfoldPack? body with
        | some u => descend cx u (path ++ (List.replicate xs.size "λ")) opt guard true cons consL acc
        | none =>
          let concl ← renConcl cx.params body
          acc.modify fun f => { f with facts := f.facts.push s!"{cx.owner}.{cx.field}: {concl}" }
      else if !spans.isEmpty then
        let concl ← renConcl cx.params body
        let line := s!"{cx.owner}.{cx.field}: {origin}: {String.intercalate " > " spans.toList} ⇒ {concl}"
        acc.modify fun f => { f with others := f.others.push line }
    return
  if e.containsFVar cx.spStart then
    match ← unfoldPack? e with
    | some u => descend cx u path opt guard true cons consL acc
    | none =>
      let concl ← renConcl cx.params e
      acc.modify fun f => { f with facts := f.facts.push s!"{cx.owner}.{cx.field}: {concl}" }

/-- Every closure of a constructor's fields (the inductive's parameters and
    the non-`Prop` fields skipped). -/
def ctorClosures (ctor : Name) : MetaM Found := do
  let some ci := (← getEnv).find? ctor | throwError "{ctor}: missing"
  forallTelescope ci.type fun xs _ => do
    let acc ← IO.mkRef ({} : Found)
    let mut spStart : Option FVarId := none
    for x in xs do
      if (← x.fvarId!.getDecl).userName == `sp_start then spStart := some x.fvarId!
    let some sp := spStart | throwError "{ctor}: no sp_start"
    for i in [:xs.size] do
      let x := xs[i]!
      let t := (← inferType x).consumeMData
      if !(← isProp t) then continue
      let nm := (← x.fvarId!.getDecl).userName.toString
      descend { owner := short ctor, field := nm, fieldIdx := i, params := xs, spStart := sp }
        t [] false false false #[] #[] acc
    acc.get

/-- The spines of one hypothesis's type, read against a producer's telescope. -/
def spinesOfHyp (params : Array Expr) (spStart : FVarId) (h : FVarId) : MetaM (Array String) := do
  let d ← h.getDecl
  let acc ← IO.mkRef ({} : Found)
  descend { owner := "", field := d.userName.toString, fieldIdx := 0, params, spStart }
    d.type.consumeMData [] false false false #[] #[] acc
  return (← acc.get).closures.map (·.spine)

/-! ## §2 What the exits build -/

/-- Casts only — a lambda is the closure itself. -/
partial def peelC (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Eq.mpr 4 || e.isAppOfArity ``Eq.mp 4 || e.isAppOfArity ``cast 4 then
    peelC (e.getArg! 3)
  else if e.isAppOfArity ``Eq.ndrec 6 || e.isAppOfArity ``Eq.rec 6 then peelC (e.getArg! 3)
  else if e.isAppOfArity ``Eq.subst 6 then peelC (e.getArg! 5)
  else if e.isAppOfArity ``id 2 then peelC (e.getArg! 1)
  else e

/-- Resolve a term through casts and `have` values.  `some name` when it
    bottoms in a hypothesis or an obtained variable (a forward). -/
partial def resolve (params : Array Expr) (e : Expr) : MetaM (Expr × Option String) := do
  let e := peelC e
  match e with
  | .fvar id =>
    let d ← id.getDecl
    if params.contains e then return (e, some s!"param:{d.userName}")
    match d.value? with
    | some v => resolve params v
    | none => return (e, some s!"obtained:{d.userName}")
  | _ => return (e, none)

/-- The leaves a term reaches: its free variables, `have` values expanded,
    down to the hypotheses and obtained variables that carry no value. -/
partial def leavesOf (e : Expr) (seen : IO.Ref (Std.HashSet FVarId))
    (out : IO.Ref (Array FVarId)) : MetaM Unit := do
  for id in (Lean.collectFVars {} e).fvarIds do
    if (← seen.get).contains id then continue
    seen.modify (·.insert id)
    match (← id.getDecl).value? with
    | some v => leavesOf v seen out
    | none => out.modify (·.push id)

/-- What a closure argument is derived from.  `stream`: it reaches one of the
    producer's own `SLYamlStream sp_start _` hypotheses — the absorbed stream,
    which an open entry does not supply.  `carry`: it reaches only what speaks
    of `sp_start` otherwise — the input park, its fields, a stream a callee
    derived — and rides a promise re-routed upstream.  `closed`: neither. -/
def usage (params : Array Expr) (spStart : FVarId) (e : Expr) : MetaM String := do
  let seen ← IO.mkRef ({} : Std.HashSet FVarId)
  let out ← IO.mkRef (#[] : Array FVarId)
  leavesOf e seen out
  let mut s := false
  let mut o := false
  for id in ← out.get do
    let ty := (← id.getDecl).type.consumeMData
    if !ty.containsFVar spStart then continue
    if ty.isAppOfArity ``SLYamlStream 2 && params.any (·.fvarId! == id) then s := true else o := true
  return if s then "stream" else if o then "carry" else "closed"

/-- Follow a closure's path into the argument that fills its field, as far as
    the term is literal; where it stops, read what the term is derived from. -/
partial def classify (params : Array Expr) (spStart : FVarId) (path : List String) (e : Expr) :
    MetaM String := do
  let (e, fwd) ← resolve params e
  if fwd.isSome then return "fwd"
  match path with
  | [] => usage params spStart e
  | s :: rest =>
    if s == "λ" then
      match e with
      | .lam _ _ b _ => classify params spStart rest b
      | _ => usage params spStart e
    else if s == "L" then
      if e.isAppOfArity ``Or.inl 3 then classify params spStart rest (e.getArg! 2)
      else if e.isAppOfArity ``Or.inr 3 then return "punt"
      else usage params spStart e
    else if s == "R" then
      if e.isAppOfArity ``Or.inr 3 then classify params spStart rest (e.getArg! 2)
      else if e.isAppOfArity ``Or.inl 3 then return "punt"
      else usage params spStart e
    else if s == "E" then
      if e.isAppOfArity ``Exists.intro 4 then classify params spStart rest (e.getArg! 3)
      else usage params spStart e
    else
      let i := s.toNat!
      let mut cur := e
      let mut k := i
      while k > 1 do
        let (c, f) ← resolve params cur
        if f.isSome then return "fwd"
        if c.isAppOfArity ``And.intro 4 then
          cur := c.getArg! 3; k := k - 1
        else return (← usage params spStart c)
      let (c, f) ← resolve params cur
      if f.isSome then return "fwd"
      if c.isAppOfArity ``And.intro 4 then classify params spStart rest (c.getArg! 2)
      else classify params spStart rest c

/-- Find an application of `head` in `e`, looking through `have` values. -/
partial def findDeep (head : Name) (e : Expr) (seen : IO.Ref (Std.HashSet FVarId)) :
    MetaM (Option Expr) := do
  if let some r := e.find? (·.isAppOf head) then return some r
  for id in (Lean.collectFVars {} e).fvarIds do
    if (← seen.get).contains id then continue
    seen.modify (·.insert id)
    if let some v := (← id.getDecl).value? then
      if let some r ← findDeep head v seen then return some r
  return none

/-- The spines of a constant's parameter, read against its own telescope. -/
def routeParamSpines (callee : Name) (param : String) : MetaM (Array String) := do
  let some ci := (← getEnv).find? callee | return #[]
  forallTelescope ci.type fun xs _ => do
    let mut sp : Option FVarId := none
    let mut h : Option FVarId := none
    for x in xs do
      let nm := (← x.fvarId!.getDecl).userName
      if nm == `sp_start then sp := some x.fvarId!
      if nm.toString == param then h := some x.fvarId!
    match sp, h with
    | some spId, some hId => spinesOfHyp xs spId hId
    | _, _ => return #[]

/-- Which explicit parameters of a constant are ROUTES — a type that holds a
    closure from the constant's own `sp_start` — whether its conclusion
    builds a park, and its arity. -/
def routeParams (n : Name) : MetaM (Array (Nat × String) × Bool × Nat) := do
  let some ci := (← getEnv).find? n | return (#[], false, 0)
  let mut cand : Array (Nat × String) := #[]
  let mut t := ci.type
  let mut i := 0
  while t.isForall do
    match t with
    | .forallE x d b bi =>
      let d := d.consumeMData
      if bi.isExplicit && (d.find? (·.isConstOf ``SLYamlStream)).isSome &&
          !d.isAppOfArity ``SLYamlStream 2 then
        cand := cand.push (i, x.toString)
      t := b; i := i + 1
    | _ => break
  let park := (t.find? (·.isConstOf ``PendingNode)).isSome
  let mut out : Array (Nat × String) := #[]
  for (j, x) in cand do
    unless (← routeParamSpines n x).isEmpty do out := out.push (j, x)
  return (out, park, i)

/-- One exit: its park, each closure's class, what closed the park, and the
    flow base's routes when a stack is opened at the exit. -/
structure Site where
  producer : String
  slot : String
  park : String
  stream : String
  /-- The spine of the hypothesis that produced a bound stream; `lemma:` for
      an absorption; `obtained`; empty for the producer's own stream. -/
  closedBy : String
  slots : Array (Closure × String)
  flowSlots : Array (Closure × String)
  /-- The head of an opened flow stack whose base is not a literal
      `FlowBaseRoutes.mk`. -/
  flowHead : String := ""
  /-- Obtained streams (no value, not a hypothesis) that a `carry` slot
      reaches: a derivation this walk cannot see. -/
  viaObtained : Array String := #[]
  deriving Inhabited

/-- The obtained stream leaves a term reaches. -/
def obtainedStreams (params : Array Expr) (spStart : FVarId) (e : Expr) : MetaM (Array String) := do
  let seen ← IO.mkRef ({} : Std.HashSet FVarId)
  let out ← IO.mkRef (#[] : Array FVarId)
  leavesOf e seen out
  let mut r : Array String := #[]
  for id in ← out.get do
    let d ← id.getDecl
    let ty := d.type.consumeMData
    if ty.isAppOfArity ``SLYamlStream 2 && ty.containsFVar spStart && !params.any (·.fvarId! == id) then
      r := r.push d.userName.toString
  return r

/-- A route argument at a call site. -/
structure RouteArg where
  producer : String
  callee : Name
  param : String
  cls : String
  deriving Inhabited

/-- A park or a flow base constructed anywhere in a walked body. -/
structure Build where
  producer : String
  ctor : String
  slots : Array (Closure × String)
  deriving Inhabited

def classifyCtor (table : Std.HashMap Name (Array Closure)) (params : Array Expr) (spStart : FVarId)
    (n : Name) (args : Array Expr) : MetaM (Array (Closure × String)) := do
  let mut out : Array (Closure × String) := #[]
  if let some cls := table.get? n then
    for cl in cls do
      let k ← if h : cl.fieldIdx < args.size then classify params spStart cl.path args[cl.fieldIdx]
        else pure "missing"
      out := out.push (cl, k)
  return out

def walk (table : Std.HashMap Name (Array Closure)) (c : Name) :
    MetaM (Array Site × Nat × Nat × Array RouteArg × Array Name × Array Build) := do
  let some ci := (← getEnv).find? c | throwError "{c}: missing"
  let some v := ci.value? (allowOpaque := true) | throwError "{c}: no value"
  lambdaTelescope v fun params body => do
    let mut spStart? : Option FVarId := none
    for x in params do
      if (← x.fvarId!.getDecl).userName == `sp_start then spStart? := some x.fvarId!
    -- a producer with no `sp_start` of its own (the initial state's builder,
    -- the readers) has no exit to read
    let some spStart := spStart? | return (#[], 0, 0, #[], #[], #[])
    let mut carrierH : Option Expr := none
    for x in params do
      if (← inferType x).consumeMData.isAppOfArity ``BlockStack 2 then carrierH := some x
    let sites ← IO.mkRef (#[] : Array Site)
    let slots ← IO.mkRef 0
    let nils ← IO.mkRef 0
    let routeArgs ← IO.mkRef (#[] : Array RouteArg)
    let parkBuilders ← IO.mkRef (#[] : Array Name)
    let builds ← IO.mkRef (#[] : Array Build)
    let rpCache ← IO.mkRef ({} : Std.HashMap Name (Array (Nat × String) × Bool × Nat))
    let skip (n : Name) : Bool :=
      n == ``And.intro || n == ``Or.inl || n == ``Or.inr || n == ``Exists.intro ||
      (n.toString.splitOn ".match_").length > 1 || n.isInternal ||
      (`L4YAML.Proofs.StreamAccum.PendingNode).isPrefixOf n || n == ``FlowBaseRoutes.mk
    forEachExpr' body fun e => do
      -- `forEachExpr'` visits every partial application; only a FULL one is a
      -- construction or a call
      if let .const n _ := e.getAppFn then
        if e.isApp then
          let (rps, park, arity) ← match (← rpCache.get).get? n with
            | some r => pure r
            | none =>
              let r ← routeParams n
              rpCache.modify (·.insert n r); pure r
          if e.getAppNumArgs == arity then
            -- every park or flow base constructed here
            if table.contains n then
              let slots ← classifyCtor table params spStart n e.getAppArgs
              builds.modify (·.push { producer := short c, ctor := short n, slots })
            -- call sites: every route-typed argument handed to a lemma
            if !skip n then
              let args := e.getAppArgs
              for (i, pn) in rps do
                if h : i < args.size then
                  let (_, fwd) ← resolve params args[i]
                  let cls ← if fwd.isSome then pure "fwd" else usage params spStart args[i]
                  routeArgs.modify (·.push { producer := short c, callee := n, param := pn, cls })
              if park then parkBuilders.modify fun a => if a.contains n then a else a.push n
      if e.isAppOfArity ``And.intro 4 then
        let A := (e.getArg! 0).consumeMData
        let r := (e.getArg! 3).consumeMData
        if A.isAppOf ``SLYamlStream && r.isAppOfArity ``And.intro 4 &&
            (r.getArg! 0).consumeMData.isAppOf ``BlockStack then
          slots.modify (· + 1)
          let l := (r.getArg! 2).consumeMData
          let slot := if l.isAppOfArity ``BlockStack.nil 1 then "nil"
            else if carrierH == some l then "carrier" else "forward"
          if slot == "nil" then nils.modify (· + 1)
          let streamE := e.getArg! 2
          let stream ← headOf params {} streamE
          let r2 := (r.getArg! 3).consumeMData
          let flowE := if r2.isAppOfArity ``And.intro 4 then some (r2.getArg! 2) else none
          let parkE := if r2.isAppOfArity ``And.intro 4 then
              let r3 := (r2.getArg! 3).consumeMData
              if r3.isAppOfArity ``And.intro 4 then some (r3.getArg! 2) else none
            else none
          -- the flow base's routes, when a stack is opened at this exit
          let mut flowSlots : Array (Closure × String) := #[]
          let mut flowHead := ""
          if let some f := flowE then
            let (fr, _) ← resolve params f
            let seen ← IO.mkRef ({} : Std.HashSet FVarId)
            if let some app ← findDeep ``FlowBaseRoutes.mk fr seen then
              flowSlots ← classifyCtor table params spStart ``FlowBaseRoutes.mk app.getAppArgs
            else if !(fr.isAppOf ``FlowStackB.nil) then
              flowHead ← headOf params {} f
          if slot != "nil" then
            unless flowSlots.isEmpty do
              let site : Site := { producer := short c, slot, park := "", stream, closedBy := "",
                                   slots := #[], flowSlots, flowHead }
              sites.modify (·.push site)
            return true
          -- the park and its closures
          let mut park := "?"
          let mut slotsHere : Array (Closure × String) := #[]
          if let some p := parkE then
            let (pr, fwd) ← resolve params p
            match fwd, pr.getAppFn with
            | none, .const n _ =>
              park := shortPark n
              slotsHere ← classifyCtor table params spStart n pr.getAppArgs
            | some f, _ => park := s!"bound:{f}"
            | none, _ => park := "other"
          -- what closed the park: the bound stream's head hypothesis
          let mut closedBy := ""
          let (se, sf) ← resolve params streamE
          match sf with
          | some f => if f.startsWith "obtained:" then closedBy := "obtained"
          | none =>
            match se.getAppFn with
            | .fvar id =>
              let ss ← spinesOfHyp params spStart id
              let nm := (← id.getDecl).userName
              closedBy := if ss.isEmpty then s!"hyp:{nm}" else String.intercalate " | " ss.toList
            | .const n _ => closedBy := s!"lemma:{short n}"
            | _ => closedBy := "?"
          -- carries that reach an obtained stream
          let mut via : Array String := #[]
          if let some p := parkE then
            let (pr, fwd) ← resolve params p
            if fwd.isNone then
              if let .const n _ := pr.getAppFn then
                if let some cls := table.get? n then
                  let args := pr.getAppArgs
                  for (cl, k) in slotsHere do
                    if k == "carry" then
                      if h : cl.fieldIdx < args.size then
                        for o in ← obtainedStreams params spStart args[cl.fieldIdx] do
                          if !via.contains o then via := via.push o
                  let _ := cls
          sites.modify (·.push { producer := short c, slot, park, stream, closedBy, slots := slotsHere, flowSlots,
                                 flowHead, viaObtained := via })
      return true
    return (← sites.get, ← slots.get, ← nils.get, ← routeArgs.get, ← parkBuilders.get, ← builds.get)

/-! ## §4 The pins -/

def expectedClosures : List String :=
  ["pendingContent.h_closable[] req+guard: sp_scan: SSLComments ⇒ Stream",
   "pendingContent.h_key[λλLEEE1] req+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) ⇒ Stream",
   "pendingContent.h_key[λλLEEE5LE] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingContent.h_key[λλLEEE6LE3] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹Stream",
   "pendingContent.h_key[λλLEEE7LEE3] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingContent.h_key[λλLEEE8LEE2] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹SeqEntryTail(_)",
   "pendingContent.h_vpack[LE] opt: sp_scan: SSLComments > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingContent.h_framesS[LE2] opt: sp_scan: SSLComments ⇒ Resume(_)▹Stream",
   "pendingContent.h_framesV[LEE2] opt: sp_scan: SSLComments ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingContent.h_seqF[LEEE2] opt: sp_scan: SSLComments > SCompactMapTail(_) ⇒ Resume(_)▹SeqEntryTail(_)",
   "pendingProps.h_route[] req+guard: sp_node: SBlockNode(n,blockIn) ⇒ Stream",
   "pendingProps.h_key[L1E1] req+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] sp_p: SBlockMapEntry(_) ⇒ Stream",
   "pendingProps.h_key[L1E3LE] opt+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] sp_p: SBlockMapEntry(_) > SCompactMapTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingProps.h_key[L1E4LE3] opt+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] sp_p: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹Stream",
   "pendingProps.h_key[L1E5LEE3] opt+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] sp_p: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingProps.h_kslot[LE] opt: sp_node: SBlockNode(n,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingProps.h_routeE[LE2] opt: [n=_+1] sp_node: SBlockNode(n,blockIn) > SCompactSeqTail(_) ⇒ Stream",
   "pendingProps.h_kslotE[LEE2] opt: [n=_+1] sp_node: SBlockNode(n,blockIn) > SCompactSeqTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingProps.h_closeFE[LEE4] opt: [n=_+1] sp_node: SBlockNode(n,blockIn) > SCompactSeqTail(_) ⇒ Resume(_)▹Stream",
   "pendingProps.h_closeF[LE2] opt: sp_node: SBlockNode(n,blockIn) ⇒ Resume(_)▹Stream",
   "pendingProps.h_closeFV[LEE2] opt: sp_node: SBlockNode(n,blockIn) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingProps.h_closeFEV[LEEE2] opt: [n=_+1] sp_node: SBlockNode(n,blockIn) > SCompactSeqTail(_) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingDocStart.h_doc_route[] req: sp_scan: GAlt(SLBareDocument,GSeq(SENode,SSLComments)) ⇒ Stream",
   "pendingDirective.h_dir_route[] req: sp_block: SLDirectiveDocument ⇒ Stream",
   "pendingBlockContent.h_closable[] req+guard: sp_scan: SSLComments ⇒ Stream",
   "pendingBlockContent.h_closable_entry[] req: sp_scan: SSLComments > SCompactSeqTail(n) ⇒ Stream",
   "pendingBlockContent.h_key[λλLEEE1] req+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) ⇒ Stream",
   "pendingBlockContent.h_key[λλLEEE5LE] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingBlockContent.h_key[λλLEEE6LE3] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹Stream",
   "pendingBlockContent.h_key[λλLEEE7LEE3] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingBlockContent.h_key[λλLEEE8LEE2] opt+guard+pack: [col(pos(simpleKey(sc)))=_; line(pos(simpleKey(sc)))=line(sc)] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹SeqEntryTail(_)",
   "pendingBlockContent.h_kslot[LE] opt: sp_scan: SSLComments > SCompactSeqTail(n) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingBlockContent.h_closeF[LE3] opt: sp_scan: SSLComments > SCompactSeqTail(n) ⇒ Resume(_)▹Stream",
   "pendingBlockContent.h_seqF[LE] opt: sp_scan: SSLComments > SCompactSeqTail(n) ⇒ SeqEntryTail(_)",
   "pendingBlockContent.h_kslotUp[LE] opt: sp_scan: SSLComments > SCompactSeqTail(n) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingBlockContent.h_closeFV[LEE] opt: sp_scan: SSLComments > SCompactSeqTail(n) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingBlock.h_close[] req: sp_scan: SBlockIndented(n,blockIn) ⇒ Stream",
   "pendingBlock.h_close_entry[] req: sp_scan: SBlockIndented(n,blockIn) > SCompactSeqTail(n) ⇒ Stream",
   "pendingBlock.h_kslot[LE] opt: sp_scan: SBlockIndented(n,blockIn) > SCompactSeqTail(n) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingBlock.h_closeF[LE3] opt: sp_scan: SBlockIndented(n,blockIn) > SCompactSeqTail(n) ⇒ Resume(_)▹Stream",
   "pendingBlock.h_seqF[LE] opt: sp_scan: SBlockIndented(n,blockIn) > SCompactSeqTail(n) ⇒ SeqEntryTail(_)",
   "pendingBlock.h_kslotUp[LE] opt: sp_scan: SBlockIndented(n,blockIn) > SCompactSeqTail(n) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingBlock.h_closeFV[LEE] opt: sp_scan: SBlockIndented(n,blockIn) > SCompactSeqTail(n) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingMapValue.h_close[] req: sp_scan: SBlockNode(n+1,blockIn) ⇒ Stream",
   "pendingMapValue.h_ivl[R2] req: [col(sp_scan)=n+1] sp_scan: SBlockIndented(n,blockOut) ⇒ Stream",
   "pendingMapValue.h_expl[LE2] opt: _: SBlockMapEntry(n) ⇒ Stream",
   "pendingMapValue.h_vslot[L3] opt: [col(sp_scan)=n+1] sp_scan: SBlockIndented(n,blockOut) ⇒ Stream",
   "pendingMapValue.h_kslot[LE] opt: sp_scan: SBlockNode(n+1,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "pendingMapValue.h_closeF[LE3] opt: sp_scan: SBlockNode(n+1,blockIn) ⇒ Resume(n::_)▹Stream",
   "pendingMapValue.h_frames[LE2] opt: sp_scan: SSLComments ⇒ Resume(_)▹Stream",
   "pendingMapValue.h_closeFV[LEE3] opt: sp_scan: SBlockNode(n+1,blockIn) ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingMapValue.h_framesV[LEE2] opt: sp_scan: SSLComments ⇒ Resume(_)▹ExplValueLine(_)",
   "pendingMapValue.h_seqF[LEE2] opt: sp_scan: SBlockNode(n+1,blockIn) > SCompactMapTail(n) ⇒ Resume(_)▹SeqEntryTail(_)",
   "pendingMapValue.h_explUp[LEE2] opt: _: SBlockMapEntry(n) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "mk.value[] req+guard: sp_br: SFlowContent(n,flowOut) > SSLComments ⇒ Stream",
   "mk.key[LEE1] opt: [kc=_] _: SBlockMapEntry(_) ⇒ Stream",
   "mk.key[LEE4LE] opt: [kc=_] _: SBlockMapEntry(_) > SCompactMapTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream",
   "mk.key[LEE5LE2] opt: [kc=_] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹Stream",
   "mk.key[LEE6LEE2] opt: [kc=_] _: SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹ExplValueLine(_)",
   "mk.vslot[LE] opt: sp_br: SFlowContent(n,flowOut) > SSLComments > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream"]
def expectedSpines : List String :=
  ["  stream=0 carry=16 fwd=0 punt=0 closed=0 SSLComments ⇒ Stream  ← pendingContent.h_closable, pendingBlockContent.h_closable",
   "  stream=0 carry=18 fwd=0 punt=0 closed=4 [col(pos(simpleKey(_)))=_; line(pos(simpleKey(_)))=line(_)] SBlockMapEntry(_) ⇒ Stream  ← pendingContent.h_key, pendingProps.h_key, pendingBlockContent.h_key",
   "  stream=0 carry=18 fwd=0 punt=0 closed=4 [col(pos(simpleKey(_)))=_; line(pos(simpleKey(_)))=line(_)] SBlockMapEntry(_) > SCompactMapTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingContent.h_key, pendingProps.h_key, pendingBlockContent.h_key",
   "  stream=0 carry=18 fwd=0 punt=0 closed=4 [col(pos(simpleKey(_)))=_; line(pos(simpleKey(_)))=line(_)] SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹Stream  ← pendingContent.h_key, pendingProps.h_key, pendingBlockContent.h_key",
   "  stream=0 carry=18 fwd=0 punt=0 closed=4 [col(pos(simpleKey(_)))=_; line(pos(simpleKey(_)))=line(_)] SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹ExplValueLine(_)  ← pendingContent.h_key, pendingProps.h_key, pendingBlockContent.h_key",
   "  stream=0 carry=12 fwd=0 punt=0 closed=4 [col(pos(simpleKey(_)))=_; line(pos(simpleKey(_)))=line(_)] SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Resume(_)▹SeqEntryTail(_)  ← pendingContent.h_key, pendingBlockContent.h_key",
   "  stream=0 carry=8 fwd=0 punt=2 closed=0 SSLComments > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingContent.h_vpack",
   "  stream=0 carry=12 fwd=0 punt=4 closed=0 SSLComments ⇒ Resume(_)▹Stream  ← pendingContent.h_framesS, pendingMapValue.h_frames",
   "  stream=1 carry=11 fwd=0 punt=4 closed=0 SSLComments ⇒ Resume(_)▹ExplValueLine(_)  ← pendingContent.h_framesV, pendingMapValue.h_framesV",
   "  stream=0 carry=3 fwd=0 punt=7 closed=0 SSLComments > SCompactMapTail(_) ⇒ Resume(_)▹SeqEntryTail(_)  ← pendingContent.h_seqF",
   "  stream=0 carry=6 fwd=0 punt=0 closed=0 SBlockNode(_,blockIn) ⇒ Stream  ← pendingProps.h_route",
   "  stream=0 carry=2 fwd=2 punt=2 closed=0 SBlockNode(_,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingProps.h_kslot",
   "  stream=0 carry=1 fwd=2 punt=3 closed=0 [_=_+1] SBlockNode(_,blockIn) > SCompactSeqTail(_) ⇒ Stream  ← pendingProps.h_routeE",
   "  stream=0 carry=1 fwd=2 punt=3 closed=0 [_=_+1] SBlockNode(_,blockIn) > SCompactSeqTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingProps.h_kslotE",
   "  stream=0 carry=3 fwd=0 punt=3 closed=0 [_=_+1] SBlockNode(_,blockIn) > SCompactSeqTail(_) ⇒ Resume(_)▹Stream  ← pendingProps.h_closeFE",
   "  stream=0 carry=3 fwd=0 punt=3 closed=0 SBlockNode(_,blockIn) ⇒ Resume(_)▹Stream  ← pendingProps.h_closeF",
   "  stream=0 carry=3 fwd=0 punt=3 closed=0 SBlockNode(_,blockIn) ⇒ Resume(_)▹ExplValueLine(_)  ← pendingProps.h_closeFV",
   "  stream=0 carry=1 fwd=2 punt=3 closed=0 [_=_+1] SBlockNode(_,blockIn) > SCompactSeqTail(_) ⇒ Resume(_)▹ExplValueLine(_)  ← pendingProps.h_closeFEV",
   "  stream=0 carry=0 fwd=0 punt=0 closed=0 GAlt(SLBareDocument,GSeq(SENode,SSLComments)) ⇒ Stream  ← pendingDocStart.h_doc_route",
   "  stream=0 carry=0 fwd=0 punt=0 closed=0 SLDirectiveDocument ⇒ Stream  ← pendingDirective.h_dir_route",
   "  stream=0 carry=6 fwd=0 punt=0 closed=0 SSLComments > SCompactSeqTail(_) ⇒ Stream  ← pendingBlockContent.h_closable_entry",
   "  stream=0 carry=9 fwd=0 punt=3 closed=0 SSLComments > SCompactSeqTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingBlockContent.h_kslot, pendingBlockContent.h_kslotUp",
   "  stream=0 carry=6 fwd=0 punt=0 closed=0 SSLComments > SCompactSeqTail(_) ⇒ Resume(_)▹Stream  ← pendingBlockContent.h_closeF",
   "  stream=0 carry=3 fwd=0 punt=3 closed=0 SSLComments > SCompactSeqTail(_) ⇒ SeqEntryTail(_)  ← pendingBlockContent.h_seqF",
   "  stream=0 carry=6 fwd=0 punt=0 closed=0 SSLComments > SCompactSeqTail(_) ⇒ Resume(_)▹ExplValueLine(_)  ← pendingBlockContent.h_closeFV",
   "  stream=0 carry=7 fwd=0 punt=0 closed=0 SBlockIndented(_,blockIn) ⇒ Stream  ← pendingBlock.h_close",
   "  stream=0 carry=7 fwd=0 punt=0 closed=0 SBlockIndented(_,blockIn) > SCompactSeqTail(_) ⇒ Stream  ← pendingBlock.h_close_entry",
   "  stream=0 carry=12 fwd=0 punt=2 closed=0 SBlockIndented(_,blockIn) > SCompactSeqTail(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingBlock.h_kslot, pendingBlock.h_kslotUp",
   "  stream=0 carry=3 fwd=0 punt=4 closed=0 SBlockIndented(_,blockIn) > SCompactSeqTail(_) ⇒ Resume(_)▹Stream  ← pendingBlock.h_closeF",
   "  stream=0 carry=1 fwd=0 punt=6 closed=0 SBlockIndented(_,blockIn) > SCompactSeqTail(_) ⇒ SeqEntryTail(_)  ← pendingBlock.h_seqF",
   "  stream=0 carry=5 fwd=0 punt=2 closed=0 SBlockIndented(_,blockIn) > SCompactSeqTail(_) ⇒ Resume(_)▹ExplValueLine(_)  ← pendingBlock.h_closeFV",
   "  stream=2 carry=4 fwd=0 punt=0 closed=0 SBlockNode(_+1,blockIn) ⇒ Stream  ← pendingMapValue.h_close",
   "  stream=2 carry=4 fwd=0 punt=6 closed=0 [col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream  ← pendingMapValue.h_ivl, pendingMapValue.h_vslot",
   "  stream=1 carry=1 fwd=0 punt=4 closed=0 SBlockMapEntry(_) ⇒ Stream  ← pendingMapValue.h_expl",
   "  stream=0 carry=4 fwd=0 punt=2 closed=0 SBlockNode(_+1,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingMapValue.h_kslot",
   "  stream=0 carry=4 fwd=0 punt=2 closed=0 SBlockNode(_+1,blockIn) ⇒ Resume(_::_)▹Stream  ← pendingMapValue.h_closeF",
   "  stream=2 carry=2 fwd=0 punt=2 closed=0 SBlockNode(_+1,blockIn) ⇒ Resume(_)▹ExplValueLine(_)  ← pendingMapValue.h_closeFV",
   "  stream=0 carry=1 fwd=0 punt=5 closed=0 SBlockNode(_+1,blockIn) > SCompactMapTail(_) ⇒ Resume(_)▹SeqEntryTail(_)  ← pendingMapValue.h_seqF",
   "  stream=0 carry=1 fwd=0 punt=5 closed=0 SBlockMapEntry(_) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← pendingMapValue.h_explUp"]
def expectedSites : List String :=
  ["  accum_block_on_closeThenBlock: nil park=pendingBlock stream=bound:h_stream_new:=param:h_close_pending closedBy=[SSLComments ⇒ Stream] h_close=carry,h_close_entry=carry,h_kslot=carry,h_closeF=carry,h_seqF=punt,h_kslotUp=carry,h_closeFV=carry",
   "  accum_block_on_closeThenBlock: nil park=pendingBlock stream=bound:h_stream_a closedBy=[obtained] h_close=carry,h_close_entry=carry,h_kslot=carry,h_closeF=punt,h_seqF=punt,h_kslotUp=carry,h_closeFV=punt",
   "  block_dispatch_deferred: nil park=pendingFlow stream=param:h_stream closedBy=[] ",
   "  compact_open_map: nil park=pendingMapValue stream=param:h_stream_block closedBy=[] h_close=carry,h_ivl=carry,h_expl=carry,h_vslot=carry,h_kslot=punt,h_closeF=punt,h_frames=punt,h_closeFV=punt,h_framesV=punt,h_seqF=punt,h_explUp=punt",
   "  colon_open_map_explicit: nil park=pendingMapValue stream=param:h_stream_mid closedBy=[] h_close=carry,h_ivl=carry,h_expl=punt,h_vslot=carry,h_kslot=punt,h_closeF=punt,h_frames=punt,h_closeFV=punt,h_framesV=punt,h_seqF=punt,h_explUp=punt",
   "  question_open_map: nil park=pendingMapValue stream=param:h_stream_land closedBy=[] h_close=stream,h_ivl=stream,h_expl=stream,h_vslot=stream,h_kslot=carry,h_closeF=carry,h_frames=carry,h_closeFV=stream,h_framesV=stream,h_seqF=punt,h_explUp=carry",
   "  colon_open_map: nil park=pendingMapValue stream=param:h_stream_land closedBy=[] h_close=stream,h_ivl=punt,h_expl=punt,h_vslot=punt,h_kslot=carry,h_closeF=carry,h_frames=carry,h_closeFV=stream,h_framesV=carry,h_seqF=punt,h_explUp=punt",
   "  accum_block_on_noPending: nil park=pendingBlock stream=param:h_stream_block closedBy=[] h_close=carry,h_close_entry=carry,h_kslot=punt,h_closeF=carry,h_seqF=punt,h_kslotUp=punt,h_closeFV=punt",
   "  accum_block_on_pendingBlock: nil park=pendingBlock stream=param:h_stream_block closedBy=[] h_close=carry,h_close_entry=carry,h_kslot=carry,h_closeF=punt,h_seqF=punt,h_kslotUp=carry,h_closeFV=carry",
   "  accum_block_on_pendingBlock: nil park=pendingBlock stream=param:h_stream_block closedBy=[] h_close=carry,h_close_entry=carry,h_kslot=carry,h_closeF=punt,h_seqF=carry,h_kslotUp=carry,h_closeFV=carry",
   "  accum_block_on_pendingBlock: nil park=pendingBlock stream=param:h_stream_block closedBy=[] h_close=carry,h_close_entry=carry,h_kslot=carry,h_closeF=punt,h_seqF=punt,h_kslotUp=carry,h_closeFV=carry",
   "  accum_block_on_pendingBlockContent: nil park=pendingBlock stream=param:h_stream_block closedBy=[] h_close=carry,h_close_entry=carry,h_kslot=carry,h_closeF=carry,h_seqF=punt,h_kslotUp=carry,h_closeFV=carry",
   "  colon_open_map_implicit: nil park=pendingMapValue stream=param:h_stream_block closedBy=[] h_close=carry,h_ivl=punt,h_expl=punt,h_vslot=punt,h_kslot=carry,h_closeF=carry,h_frames=carry,h_closeFV=carry,h_framesV=carry,h_seqF=carry,h_explUp=punt",
   "  accum_content_on_pendingBlock_indented: nil park=pendingBlockContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_closable_entry=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=carry,h_closeF=carry,h_seqF=carry,h_kslotUp=carry,h_closeFV=carry",
   "  accum_content_on_pendingBlock_indented: nil park=pendingProps stream=param:h_stream_block closedBy=[] h_route=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=carry,h_routeE=carry,h_kslotE=carry,h_closeFE=carry,h_closeF=punt,h_closeFV=punt,h_closeFEV=carry",
   "  accum_content_on_pendingBlock_indented: nil park=pendingBlockContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_closable_entry=carry,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_kslot=carry,h_closeF=carry,h_seqF=carry,h_kslotUp=carry,h_closeFV=carry",
   "  accum_content_on_pendingBlock_indented: nil park=pendingBlockContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_closable_entry=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=carry,h_closeF=carry,h_seqF=carry,h_kslotUp=carry,h_closeFV=carry",
   "  content_dispatch_routed: nil park=pendingProps stream=param:h_stream_res closedBy=[] h_route=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=punt,h_routeE=punt,h_kslotE=punt,h_closeFE=punt,h_closeF=punt,h_closeFV=punt,h_closeFEV=punt",
   "  content_dispatch_routed: nil park=pendingProps stream=param:h_stream_res closedBy=[] h_route=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=punt,h_routeE=punt,h_kslotE=punt,h_closeFE=punt,h_closeF=punt,h_closeFV=punt,h_closeFEV=punt",
   "  content_dispatch_routed: nil park=pendingContent stream=param:h_stream_res closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=punt,h_framesS=punt,h_framesV=punt,h_seqF=punt",
   "  content_dispatch_routed: nil park=pendingContent stream=param:h_stream_res closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=punt,h_framesS=punt,h_framesV=punt,h_seqF=punt",
   "  accum_content_on_pendingMapValue_indented: nil park=pendingContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=carry",
   "  accum_content_on_pendingMapValue_indented: nil park=pendingProps stream=param:h_stream_block closedBy=[] h_route=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=carry,h_routeE=punt,h_kslotE=punt,h_closeFE=punt,h_closeF=carry,h_closeFV=carry,h_closeFEV=punt",
   "  accum_content_on_pendingMapValue_indented: nil park=pendingContent stream=bound:h_stream':=param:h_close_old closedBy=[SBlockNode(_+1,blockIn) ⇒ Stream] h_closable=carry,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=carry",
   "  accum_content_on_pendingMapValue_indented: nil park=pendingContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=carry",
   "  accum_content_pending: nil park=pendingProps stream=param:h_stream_block closedBy=[] h_route=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=fwd,h_routeE=fwd,h_kslotE=fwd,h_closeFE=carry,h_closeF=carry,h_closeFV=carry,h_closeFEV=fwd",
   "  accum_content_pending: nil park=pendingProps stream=param:h_stream_block closedBy=[] h_route=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=fwd,h_routeE=fwd,h_kslotE=fwd,h_closeFE=carry,h_closeF=carry,h_closeFV=carry,h_closeFEV=fwd",
   "  accum_content_pending: nil park=pendingContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=punt",
   "  accum_content_pending: nil park=pendingContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=punt",
   "  accum_content_pending: nil park=pendingBlockContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_closable_entry=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=carry,h_closeF=carry,h_seqF=punt,h_kslotUp=punt,h_closeFV=carry",
   "  accum_content_pending: nil park=pendingContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=punt",
   "  accum_content_pending: nil park=pendingBlockContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_closable_entry=carry,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_kslot=carry,h_closeF=carry,h_seqF=punt,h_kslotUp=punt,h_closeFV=carry",
   "  accum_content_pending: nil park=pendingContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_key=closed,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=punt",
   "  accum_content_pending: nil park=pendingBlockContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_closable_entry=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_kslot=carry,h_closeF=carry,h_seqF=punt,h_kslotUp=punt,h_closeFV=carry",
   "  accum_content_pending: nil park=pendingContent stream=param:h_stream_block closedBy=[] h_closable=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_key=carry,h_vpack=carry,h_framesS=carry,h_framesV=carry,h_seqF=punt",
   "  accum_flow_open_depth0: nil park=noPending stream=bound:h_stream_mid:=bound:h_close closedBy=[SSLComments ⇒ Stream]  flow[value=carry,key=carry,key=carry,key=carry,key=carry,vslot=punt]",
   "  accum_flow_open_depth0: nil park=noPending stream=bound:h_stream_block:=L4YAML.Proofs.StreamAccum.absorb_stacksB closedBy=[lemma:absorb_stacksB]  flow=bound:h_kpkg:=Exists.intro",
   "  accum_flow_open_depth0: nil park=noPending stream=bound:h_stream_block:=L4YAML.Proofs.StreamAccum.absorb_stacksB closedBy=[lemma:absorb_stacksB]  flow[value=carry,key=carry,key=carry,key=carry,key=carry,vslot=punt]",
   "  accum_flow_open_depth0: carrier park= stream=param:h_stream closedBy=[]  flow[value=carry,key=carry,key=carry,key=carry,key=carry,vslot=carry]",
   "  accum_flow_open_depth0: nil park=noPending stream=bound:h_stream_block:=L4YAML.Proofs.StreamAccum.absorb_stacksB closedBy=[lemma:absorb_stacksB]  flow[value=carry,key=carry,key=carry,key=carry,key=carry,vslot=punt]",
   "  accum_flow_open_depth0: carrier park= stream=param:h_stream closedBy=[]  flow[value=carry,key=carry,key=carry,key=carry,key=carry,vslot=carry]",
   "  accum_flow_open_depth0: carrier park= stream=param:h_stream closedBy=[]  flow[value=carry,key=carry,key=carry,key=carry,key=carry,vslot=carry]",
   "  colon_open_map_props: nil park=pendingMapValue stream=param:h_stream_block closedBy=[] h_close=carry,h_ivl=punt,h_expl=punt,h_vslot=punt,h_kslot=carry,h_closeF=carry,h_frames=carry,h_closeFV=carry,h_framesV=carry,h_seqF=punt,h_explUp=punt",
   "  accum_structural_pending: nil park=bound:obtained:h_pend_new stream=bound:h_stream_mid:=bound:h_close closedBy=[SSLComments ⇒ Stream] ",
   "  accum_structural_pending: nil park=bound:obtained:h_pend_new stream=bound:h_stream_mid:=bound:h_close closedBy=[SSLComments ⇒ Stream] ",
   "  accum_structural_pending: nil park=bound:obtained:h_pend' stream=bound:h_stream_old closedBy=[obtained] "]
def expectedK : List String :=
  ["  SBlockNode(_+1,blockIn) ⇒ Stream  ← question_open_map:pendingMapValue.h_close, colon_open_map:pendingMapValue.h_close  [pendingMapValue.h_close]",
   "  [col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream  ← question_open_map:pendingMapValue.h_ivl, question_open_map:pendingMapValue.h_vslot, accum_block_pending→accum_block_on_closeThenBlock.h_vslot  [pendingMapValue.h_ivl, pendingMapValue.h_vslot]",
   "  SBlockMapEntry(_) ⇒ Stream  ← question_open_map:pendingMapValue.h_expl  [pendingMapValue.h_expl]",
   "  SBlockNode(_+1,blockIn) ⇒ Resume(_)▹ExplValueLine(_)  ← question_open_map:pendingMapValue.h_closeFV, colon_open_map:pendingMapValue.h_closeFV  [pendingMapValue.h_closeFV]",
   "  SSLComments ⇒ Resume(_)▹ExplValueLine(_)  ← question_open_map:pendingMapValue.h_framesV  [pendingContent.h_framesV, pendingMapValue.h_framesV]",
   "  GAlt(SLBareDocument,GSeq(SENode,SSLComments)) ⇒ Stream  ← structural_dispatch_to_pending:pendingDocStart.h_doc_route  [pendingDocStart.h_doc_route]",
   "  SBlockNode(0,blockIn) ⇒ Stream  ← content_dispatch_after_close→content_dispatch_routed.h_route, accum_content_pending→content_dispatch_routed.h_route  []",
   "  SSLComments ⇒ Stream  ← accum_content_pending→keyctx_of_preprocess.h_close, accum_content_on_noPending→keyctx_of_preprocess.h_close, accum_block_pending→accum_block_on_pendingContent.h_close_pending, accum_block_pending→accum_block_on_closeThenBlock.h_close_pending, accum_block_pending→accum_block_on_pendingBlockContent.h_close_pending, accum_block_pending→accum_block_on_pendingBlock.h_close_pending  [pendingContent.h_closable, pendingBlockContent.h_closable]",
   "  [col(_)=_+1] SBlockIndented(_,blockOut) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Stream  ← accum_block_pending→accum_block_on_closeThenBlock.h_vslot  []",
   "  SLDirectiveDocument ⇒ Stream  ← accum_structural_pending→dispatch_new_pending.h_dir_route  [pendingDirective.h_dir_route]"]
/-- Item 256 moves two closure slots from `punt` to `carry` — the root `-`'s
    and the content sibling's `pendingBlock.h_closeF` — in the slot, optional
    and build tallies alike; no site, spine or shape is added. -/
def expectedLine : String :=
  "closures=54 packed=14 optional=41 guarded=13 facts=3 others=1 byHead=6 byFirst=8 bySpine=39 flowRoutes=6 flowSpinesNew=6 slots=61 nil=43 parkedCtor=35 closureSlots=255 stream=8 carry=156 fwd=8 punt=83 closed=0 mandatory[stream=3 carry=48 fwd=0 punt=3 closed=0] optional[stream=5 carry=108 fwd=8 punt=80 closed=0] packSlots=104 pack[stream=0 carry=84 fwd=0 punt=0 closed=20] spinesFromStream=5 spinesCarried=32 spinesTouched=37 firstsFromStream=4 headsFromStream=4 streamSites=2 closings=10 closedDistinct=2 closedIn=2 absorbed=3 obtained=2 flowSites=6 flowSlots=36 flow[stream=0 carry=33 fwd=0 punt=3 closed=0] routeArgs=150 routeStream=18 routeCarry=42 routeFwd=50 routeClosed=40 routeToWalked=97 routeStreamToWalked=13 viaObtained=0 viaSites=0 builders=13 builds=169 buildSlots=1095 build[stream=9 carry=275 fwd=705 punt=86 closed=20] buildStreamSlots=9 buildSpines=6 routePairs=8 routeSpines=5 k=10 kHeads=6 streamBuilders=8"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- §1 the parks and the flow bases, statically
  let some (.inductInfo pi) := env.find? ``PendingNode | throwError "PendingNode missing"
  let mut table : Std.HashMap Name (Array Closure) := {}
  let mut closureLines : Array String := #[]
  let mut facts : Array String := #[]
  let mut others : Array String := #[]
  let mut allC : Array Closure := #[]
  for ctor in pi.ctors ++ [``FlowBaseRoutes.mk] do
    let f ← ctorClosures ctor
    table := table.insert ctor f.closures
    allC := allC ++ f.closures
    facts := facts ++ f.facts
    others := others ++ f.others
    for cl in f.closures do
      closureLines := closureLines.push s!"{cl.owner}.{cl.field}[{String.intercalate "" cl.path}] {cl.flags}: {cl.label}"
  let parkC := allC.filter (·.owner != "mk")
  let flowC := allC.filter (·.owner == "mk")
  let distinct (xs : Array String) : Array String := Id.run do
    let mut out : Array String := #[]
    for x in xs do if !out.contains x then out := out.push x
    return out
  let spines := distinct (parkC.map (·.spine))
  let firsts := distinct (parkC.map (·.first))
  let heads := distinct (parkC.map (·.head))
  let flowSpines := distinct (flowC.map (·.spine))
  let flowNew := flowSpines.filter fun s => !spines.contains s
  -- §2 the walk over item 247's producers and the five
  let walked := (Tests.Guards.ExitHandoff.expectedShare ++ Tests.Guards.ExitHandoff.expectedOutsideShare).map
    (fun s => s.toName) |>.toArray
  let walked := sorted (walked ++ (five.toArray.filter fun n => !walked.contains n))
  let mut sites : Array Site := #[]
  let mut slotsTotal := 0
  let mut nilTotal := 0
  let mut routeArgs : Array RouteArg := #[]
  let mut builderLines : Array String := #[]
  let mut builds : Array Build := #[]
  -- the 25, then every park builder they reach: a callee whose conclusion
  -- builds a park, transitively
  let mut done : Array Name := #[]
  let mut todo : List Name := walked.toList
  let mut extra : Array Name := #[]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if done.contains c then continue
    done := done.push c
    let (ss, sl, nl, ra, pb, bs) ← walk table c
    if walked.contains c then
      sites := sites ++ ss
      slotsTotal := slotsTotal + sl
      nilTotal := nilTotal + nl
    else extra := extra.push c
    routeArgs := routeArgs ++ ra
    builds := builds ++ bs
    unless pb.isEmpty do
      builderLines := builderLines.push s!"  {short c}: {String.intercalate ", " (pb.map short).toList}"
      for b in pb do if !done.contains b then todo := b :: todo
  let raWalked := routeArgs.filter fun r => walked.contains r.callee
  let raStream := routeArgs.filter (·.cls == "stream")
  let raStreamAt := tally (raStream.map fun r => s!"{r.producer}→{short r.callee}.{r.param}")
  -- the spines of the route parameters that receive a stream-built argument
  let mut routeSpines : Array String := #[]
  let mut routePairs : Array (Name × String) := #[]
  let mut routeProv : Array (String × String) := #[]   -- spine, "producer→callee.param"
  for r in raStream do
    let pair := (r.callee, r.param)
    let prov := s!"{r.producer}→{short r.callee}.{r.param}"
    for sp in ← routeParamSpines r.callee r.param do
      if !routeSpines.contains sp then routeSpines := routeSpines.push sp
      if !routeProv.contains (sp, prov) then routeProv := routeProv.push (sp, prov)
    unless routePairs.contains pair do routePairs := routePairs.push pair
  let raCarry := routeArgs.filter (·.cls == "carry")
  let raFwd := routeArgs.filter (·.cls == "fwd")
  let raClosed := routeArgs.filter (·.cls == "closed")
  let viaAll := sites.foldl (fun acc s => acc ++ s.viaObtained) (#[] : Array String)
  let viaSites := sites.filter fun s => !s.viaObtained.isEmpty
  -- every construction: exits and builders alike
  let buildSlots := builds.foldl (fun acc b => acc ++ b.slots) (#[] : Array (Closure × String))
  let buildStream := buildSlots.filter (·.2 == "stream")
  let buildSpines := Id.run do
    let mut out : Array String := #[]
    for (cl, _) in buildStream do if !out.contains cl.spine then out := out.push cl.spine
    return out
  let buildAt := tally (builds.foldl (fun acc b =>
    acc ++ ((b.slots.filter (·.2 == "stream")).map fun (cl, _) => s!"{b.producer}:{b.ctor}.{cl.field}")) #[])
  let streamBuilders := Id.run do
    let mut out : Array String := #[]
    for b in builds do
      if b.slots.any (·.2 == "stream") && !out.contains b.producer then out := out.push b.producer
    for r in raStream do if !out.contains r.producer then out := out.push r.producer
    return out
  let kSpines := Id.run do
    let mut out := buildSpines
    for sp in routeSpines do if !out.contains sp then out := out.push sp
    return out
  let headOfSpine (sp : String) : String :=
    let body := if sp.startsWith "[" then ((sp.splitOn "] ")[1]?.getD sp) else sp
    ((body.splitOn "(").head!.splitOn " ").head!
  let kHeads := Id.run do
    let mut out : Array String := #[]
    for sp in kSpines do
      let h := headOfSpine sp
      if !out.contains h then out := out.push h
    return out
  -- the k, each with where it is first built from the stream
  let mut kLines : Array String := #[]
  for sp in kSpines do
    let mut prov : Array String := #[]
    for b in builds do
      for (cl, k) in b.slots do
        if k == "stream" && cl.spine == sp then
          let pr := s!"{b.producer}:{b.ctor}.{cl.field}"
          if !prov.contains pr then prov := prov.push pr
    for (sp', pr) in routeProv do
      if sp' == sp && !prov.contains pr then prov := prov.push pr
    let owners := (parkC.filter (·.spine == sp)).map fun c => s!"{c.owner}.{c.field}"
    kLines := kLines.push s!"  {sp}  ← {String.intercalate ", " prov.toList}  [{String.intercalate ", " owners.toList}]"
  let nilSites := sites.filter (·.slot == "nil")
  -- per-spine tallies: stream / carry / fwd / punt / closed
  let tallyOf (xs : Array (Closure × String)) (pred : Closure → Bool) : Nat × Nat × Nat × Nat × Nat := Id.run do
    let mut r := (0, 0, 0, 0, 0)
    for (cl, k) in xs do
      if !pred cl then continue
      r := match k with
        | "stream" => (r.1 + 1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2)
        | "carry" => (r.1, r.2.1 + 1, r.2.2.1, r.2.2.2.1, r.2.2.2.2)
        | "fwd" => (r.1, r.2.1, r.2.2.1 + 1, r.2.2.2.1, r.2.2.2.2)
        | "punt" => (r.1, r.2.1, r.2.2.1, r.2.2.2.1 + 1, r.2.2.2.2)
        | _ => (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2 + 1)
    return r
  let allSlots := nilSites.foldl (fun acc s => acc ++ s.slots) (#[] : Array (Closure × String))
  let literal := tallyOf allSlots (fun c => !c.packed)
  let packed := tallyOf allSlots (·.packed)
  let flowAll := sites.foldl (fun acc s => acc ++ s.flowSlots) (#[] : Array (Closure × String))
  let flow := tallyOf flowAll (fun _ => true)
  let fmt (t : Nat × Nat × Nat × Nat × Nat) : String :=
    s!"stream={t.1} carry={t.2.1} fwd={t.2.2.1} punt={t.2.2.2.1} closed={t.2.2.2.2}"
  let mut spineLines : Array String := #[]
  let mut spinesFromStream : Array String := #[]
  let mut spinesCarried : Array String := #[]
  let mut spinesTouched : Array String := #[]
  for sp in spines do
    let t := tallyOf allSlots (·.spine == sp)
    let owners := (parkC.filter (·.spine == sp)).map fun c => s!"{c.owner}.{c.field}"
    spineLines := spineLines.push s!"  {fmt t} {sp}  ← {String.intercalate ", " owners.toList}"
    if t.1 > 0 then spinesFromStream := spinesFromStream.push sp
    if t.1 == 0 && (t.2.1 > 0 || t.2.2.1 > 0) then spinesCarried := spinesCarried.push sp
    if t.1 + t.2.1 + t.2.2.1 + t.2.2.2.2 > 0 then spinesTouched := spinesTouched.push sp
  let headsOf (sps : Array String) : Array String :=
    distinct (sps.map fun sp => ((parkC.find? (·.spine == sp)).map (·.head)).getD "?")
  let firstsOf (sps : Array String) : Array String :=
    distinct (sps.map fun sp => ((parkC.find? (·.spine == sp)).map (·.first)).getD "?")
  let mut siteLines : Array String := #[]
  for s in sites do
    let cls := s.slots.map fun (cl, k) => s!"{cl.field}={k}"
    let fls := s.flowSlots.map fun (cl, k) => s!"{cl.field}={k}"
    let flowS := if !fls.isEmpty then s!" flow[{String.intercalate "," fls.toList}]"
      else if s.flowHead != "" then s!" flow={s.flowHead}" else ""
    let viaS := if s.viaObtained.isEmpty then "" else s!" via[{String.intercalate "," s.viaObtained.toList}]"
    siteLines := siteLines.push s!"  {s.producer}: {s.slot} park={s.park} stream={s.stream} closedBy=[{s.closedBy}] {String.intercalate "," cls.toList}{flowS}{viaS}"
  -- §3 the closings
  let closings := nilSites.filter fun s => s.closedBy != ""
  let closedSpines := distinct ((closings.filter fun s =>
    !(s.closedBy.startsWith "lemma:" || s.closedBy == "obtained" || s.closedBy.startsWith "hyp:")).map (·.closedBy))
  let closedIn := closedSpines.filter spines.contains
  let absorbed := closings.filter (·.closedBy.startsWith "lemma:")
  let obtained := closings.filter (·.closedBy == "obtained")
  let flowSites := sites.filter fun s => !s.flowSlots.isEmpty
  let streamSites := nilSites.filter fun s => s.slots.any fun (cl, k) => !cl.packed && k == "stream"
  let mandatory := tallyOf allSlots (fun c => !c.packed && !c.optional)
  let optional := tallyOf allSlots (fun c => !c.packed && c.optional)
  let got := s!"closures={parkC.size} packed={(parkC.filter (·.packed)).size} optional={(parkC.filter (·.optional)).size} \
guarded={(parkC.filter (·.guarded)).size} facts={facts.size} others={others.size} \
byHead={heads.size} byFirst={firsts.size} bySpine={spines.size} flowRoutes={flowC.size} flowSpinesNew={flowNew.size} \
slots={slotsTotal} nil={nilTotal} parkedCtor={(nilSites.filter fun s => !s.slots.isEmpty).size} \
closureSlots={allSlots.size - (allSlots.filter (·.1.packed)).size} {fmt literal} \
mandatory[{fmt mandatory}] optional[{fmt optional}] \
packSlots={(allSlots.filter (·.1.packed)).size} pack[{fmt packed}] \
spinesFromStream={spinesFromStream.size} spinesCarried={spinesCarried.size} spinesTouched={spinesTouched.size} \
firstsFromStream={(firstsOf spinesFromStream).size} headsFromStream={(headsOf spinesFromStream).size} \
streamSites={streamSites.size} \
closings={closings.size} closedDistinct={closedSpines.size} closedIn={closedIn.size} absorbed={absorbed.size} obtained={obtained.size} \
flowSites={flowSites.size} flowSlots={flowAll.size} flow[{fmt flow}] \
routeArgs={routeArgs.size} routeStream={raStream.size} routeCarry={raCarry.size} routeFwd={raFwd.size} routeClosed={raClosed.size} \
routeToWalked={raWalked.size} routeStreamToWalked={(raWalked.filter (·.cls == "stream")).size} \
viaObtained={viaAll.size} viaSites={viaSites.size} \
builders={extra.size} builds={builds.size} buildSlots={buildSlots.size} \
build[{fmt (tallyOf buildSlots fun _ => true)}] buildStreamSlots={buildStream.size} \
buildSpines={buildSpines.size} routePairs={routePairs.size} routeSpines={routeSpines.size} \
k={kSpines.size} kHeads={kHeads.size} streamBuilders={streamBuilders.size}"
  logInfo m!"RouteShapes {got}\nclosures:\n{String.intercalate "\n" closureLines.toList}\n\
facts:\n{String.intercalate "\n" facts.toList}\nothers:\n{String.intercalate "\n" others.toList}\n\
heads: {String.intercalate ", " heads.toList}\nfirsts:\n{String.intercalate "\n" firsts.toList}\n\
fromStream:\n{String.intercalate "\n" spinesFromStream.toList}\n\
spines:\n{String.intercalate "\n" spineLines.toList}\n\
sites:\n{String.intercalate "\n" siteLines.toList}\n\
routeStreamAt: {raStreamAt}\nbuildAt: {buildAt}\n\
builders: {String.intercalate ", " (extra.map short).toList}\n\
streamBuilders: {String.intercalate ", " streamBuilders.toList}\n\
k:\n{String.intercalate "\n" kLines.toList}\nkHeads: {String.intercalate ", " kHeads.toList}\n\
parkBuilders:\n{String.intercalate "\n" builderLines.toList}"
  let sub := s!"slots={slotsTotal} nil={nilTotal}"
  unless (Tests.Guards.ExitHandoff.expectedLine.splitOn sub).length == 2 do
    throwError "the exits walked here are not item 247's: {sub}"
  unless closureLines.toList == expectedClosures do
    throwError "the parks' closures moved:\n{String.intercalate "\n" closureLines.toList}"
  unless spineLines.toList == expectedSpines do
    throwError "a spine's sites moved:\n{String.intercalate "\n" spineLines.toList}"
  unless siteLines.toList == expectedSites do
    throwError "an exit's hand-off moved:\n{String.intercalate "\n" siteLines.toList}"
  unless kLines.toList == expectedK do
    throwError "the spines first built from the stream moved:\n{String.intercalate "\n" kLines.toList}"
  unless got == expectedLine do
    throwError "the route-shape census moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.RouteShapes
