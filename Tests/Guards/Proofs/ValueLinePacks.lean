/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.PuntCoverInputs

/-!
# Who writes the value-line packs, and what each writer holds toward the tail at the entry's level (DOCS item 261)

Item 260 read the explicit `:` opener's lack as the field's BOTTOM: its list
is headed, so the resume needs the entry level's tail closed after the value,
and every closure the opener holds — the value-line packs its callers hand it
— closes the VALUE and the stream with it.  The carrier that would fund that
bottom without re-reading the value line as `[192]`'s empty-key entry is a
value-line-then-tail twin of those packs, and its price is the producers
touched: every position that writes a pack.  This module prices it.

**§0** finds the packs by SHAPE, not by name: a park constructor's field is a
value-line pack when its type carries, outside any `ResumeFrames`, the value
closure `∀ sp_v, SBlockIndented lvl .blockOut _ sp_v → SLYamlStream _ sp_v`
(written out, or as `ExplValueLine`); the fields that stand `ResumeFrames`
ON that closure are listed apart — frames whose bottom is a value line, the
tail BEFORE the line and not after it.  Each pack's line prints how its level
is bound, the closure's premise chain, and whether a `SCompactMapTail`
premise follows the value (the twin's shape; no pack has one).  A lemma
parameter of the same shape is a pack position too — the openers take the
packs their callers write — and §0 lists those beside the fields.  **§1**
walks every theorem for full applications of a park constructor and for
applications of a lemma with pack parameters, and at each pack position
classifies the argument: `punt` (the option's `True` arm), `stamp` (the
field's other honest arm, where it has one), `empty` (a pack over `[]`),
`relay` (a hypothesis passed through, tagged with what it is), `step` (an
`Or.imp` over one), `via` (a transport lemma, its own arguments read the
same way), or `paid` — and for a paid pack, the witness list and the closure
the pack's body spends for the value's end, read to its innermost
hypothesis: `chain` when that hypothesis is itself value-line shaped (a
destructured caller pack re-wrapped), `route` when it is a total closure
with no value line in it (the pack is BUILT here), `frames` when it is a
frames face.  **§2** reads, at every writer, each hypothesis in hand that
mentions `SCompactMapTail` or `ResumeFrames`, with its shape (item 260's
`tail(k)←…` / `frames(ks)←…`, a frames face's own bottom tagged when it is
a value line), and answers the mandate's question per row: `held` when a
held tail or frames face names a level the pack writes, `level-var` when
the pack's list is a variable no syntactic reading can enter, `none`
otherwise.  A pack body that spends a tail-premised hypothesis would be a
carrier already; the line counts those (`spendTail`).

The pins hold the eleven packs, the seven frames faces, the pack parameters,
every writer row, the per-position summary and the line.
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

namespace Tests.Guards.ValueLinePacks

/-! ## §0 The value closure, and the packs by shape -/

def sbiN : Name := ``L4YAML.Surface.SBlockIndented
def evlN : Name := ``L4YAML.Proofs.StreamAccum.ExplValueLine
def glitN : Name := ``L4YAML.Surface.GLit

/-- `∀ sp_v, SBlockIndented lvl .blockOut p sp_v → SLYamlStream s sp_v`. -/
def isValueClosure (t : Expr) : Bool :=
  match t.consumeMData with
  | .forallE _ _ (.forallE _ prem concl _) _ =>
    let prem := prem.consumeMData
    prem.isAppOfArity sbiN 4 && concl.consumeMData.isAppOfArity streamN 2 &&
      (match (prem.getArg! 1).consumeMData with | .const c _ => short c == "blockOut" | _ => false)
  | _ => false

/-- The value closure occurs in `e` outside any `ResumeFrames`. -/
partial def vcOutside (e : Expr) : Bool :=
  let e := e.consumeMData
  if isValueClosure e || e.isAppOf evlN then true
  else if e.isAppOf resumeN then false
  else match e with
    | .app f a => vcOutside f || vcOutside a
    | .forallE _ t b _ => vcOutside t || vcOutside b
    | .lam _ t b _ => vcOutside t || vcOutside b
    | .letE _ t v b _ => vcOutside t || vcOutside v || vcOutside b
    | .proj _ _ b => vcOutside b
    | _ => false

/-- `ResumeFrames` standing on the value closure occurs in `e`. -/
def framesOnVC (e : Expr) : Bool :=
  (e.find? fun s => s.isAppOfArity resumeN 3 && vcOutside (s.getArg! 0)).isSome

/-- Which arm of a pack's option carries the closure, and whether the other
    arm is `True` (a punt) or a second honest reading (a stamp). -/
def sideOf (t : Expr) : Bool × Bool :=
  let t := t.consumeMData
  if t.isAppOfArity ``Or 2 then
    let vcLeft := vcOutside (t.getArg! 0)
    let other := (if vcLeft then t.getArg! 1 else t.getArg! 0).consumeMData
    (vcLeft, other.isConstOf ``True)
  else (true, true)

/-- A proposition in one token: a relation as `l sym r`, else its head. -/
def propTok (st : Stack) (t : Expr) : String :=
  match rel t with
  | some (sym, l, r) => s!"{ppc st l}{sym}{ppc st r}"
  | none =>
    let t := t.consumeMData
    match t.getAppFn with
    | .const h _ =>
      if h == glitN && t.getAppNumArgs == 3 then s!"GLit({ppc st (t.getArg! 0)})"
      else if (`L4YAML.Surface).isPrefixOf h && t.getAppNumArgs ≥ 1 && (match (t.getArg! 0).consumeMData with | .const .. => false | _ => true) then
        s!"{short h}({ppc st (t.getArg! 0)})"
      else short h
    | _ => "?"

/-- Down through the pack's option, existentials, membership binder and
    conjunctions to the value closure: the stack there, the closure, and
    the level binding read on the way. -/
partial def peelToClosure (st : Stack) (t : Expr) (lvl : Array String) : Stack × Expr × Array String :=
  let t := t.consumeMData
  if t.isAppOfArity ``Or 2 then
    let a := t.getArg! 0
    let b := t.getArg! 1
    if vcOutside a then peelToClosure st a lvl else peelToClosure st b lvl
  else if t.isAppOfArity ``Exists 2 then
    match (t.getArg! 1).consumeMData with
    | .lam n ty body _ => peelToClosure (st.push { name := n, ty := ty, prov := none }) body (lvl.push s!"∃{bname n}")
    | _ => (st, t, lvl)
  else if t.isAppOfArity ``And 2 then
    let a := t.getArg! 0
    let b := t.getArg! 1
    if vcOutside b then peelToClosure st b (lvl.push s!"({propTok st a})")
    else peelToClosure st a (lvl.push s!"({propTok st b})")
  else match t with
    | .forallE n ty body _ =>
      if ty.consumeMData.isConstOf ``Nat then
        match body.consumeMData with
        | .forallE m mem body2 _ =>
          if mem.consumeMData.isAppOf ``Membership.mem then
            let st1 := st.push { name := n, ty := ty, prov := none }
            let mem' := mem.consumeMData
            let ns := ppc st1 (mem'.getArg! (mem'.getAppNumArgs - 2))
            peelToClosure (st1.push { name := m, ty := mem, prov := none }) body2 (lvl.push s!"∀{bname n}∈{ns}")
          else (st, t, lvl)
        | _ => (st, t, lvl)
      else (st, t, lvl)
    | _ => (st, t, lvl)

/-- The closure's premise chain, its conclusion, and whether a
    `SCompactMapTail` premise follows the value. -/
partial def premisesOf (env : Environment) (st : Stack) (t : Expr) (acc : Array String) (seenV : Bool) (tail : Bool) : Array String × String × Bool :=
  let t := t.consumeMData
  match t with
  | .forallE n ty body _ =>
    let ty' := ty.consumeMData
    let st' := st.push { name := n, ty := ty, prov := none }
    match ty'.getAppFn with
    | .const h _ =>
      if h == glitN then premisesOf env st' body (acc.push s!"GLit({ppc st (ty'.getArg! 0)})") seenV tail
      else if (`L4YAML.Surface).isPrefixOf h && ty'.getAppNumArgs ≥ 1 && levelFirst env h then
        let isV := h == sbiN
        let isT := h == tailN
        premisesOf env st' body (acc.push s!"{short h}({ppc st (ty'.getArg! 0)})") (seenV || isV) (tail || (seenV && isT))
      else if h == ``Nat || h == ``L4YAML.Surface.SurfPos then premisesOf env st' body acc seenV tail
      else premisesOf env st' body (acc.push s!"{short h}") seenV tail
    | _ => premisesOf env st' body acc seenV tail
  | _ =>
    let concl := match t.getAppFn with
      | .const h _ => if h == evlN && t.getAppNumArgs ≥ 2 then s!"ExplValueLine({ppc st (t.getArg! 1)})" else short h
      | _ => "?"
    (acc, concl, tail)

/-- Item 260's resume shape, with a frames face's own bottom tagged when it
    is a value line and a bare tail fact named. -/
partial def holdShape (env : Environment) (st : Stack) (t : Expr) (prev : Option String) : Option String :=
  let t := t.consumeMData
  match t with
  | .forallE n ty b _ =>
    let ty' := ty.consumeMData
    if ty'.isAppOfArity tailN 3 then some s!"tail({ppc st (ty'.getArg! 0)})←{prev.getD "landing"}"
    else
      let prev' := match ty'.getAppFn with
        | .const h _ => if (`L4YAML.Surface).isPrefixOf h && ty'.getAppNumArgs ≥ 1 && levelFirst env h then some s!"{short h}({ppc st (ty'.getArg! 0)})" else prev
        | _ => prev
      (holdShape env st ty prev).orElse fun _ => holdShape env (st.push { name := n, ty := ty, prov := none }) b prev'
  | .lam n ty b _ => holdShape env (st.push { name := n, ty := ty, prov := none }) b prev
  | .app .. =>
    if t.isAppOfArity resumeN 3 then
      let p := (t.getArg! 0).consumeMData
      let tag := if p.isAppOf evlN && p.getAppNumArgs ≥ 2 then s!"@ExplValueLine({ppc st (p.getArg! 1)})" else ""
      some s!"frames({ppc st (t.getArg! 1)}){tag}←{prev.getD "landing"}"
    else if t.isAppOfArity tailN 3 then some s!"tailFact({ppc st (t.getArg! 0)})"
    else t.getAppArgs.findSome? fun a => holdShape env st a prev
  | _ => none

/-- Every hypothesis in hand mentioning a tail or frames, with its shape. -/
def holdsOf (env : Environment) (stAll : Stack) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [0:stAll.size] do
    let b := stAll[i]!
    unless hasHead b.ty resumeN || hasHead b.ty tailN do continue
    let st0 := stAll.extract 0 i
    out := out.push s!"{bname b.name}:{(holdShape env st0 b.ty none).getD "?"}"
  return out

/-! ## §1 The writers -/

/-- A pack position: the argument index, the name, which arm carries the
    closure, and whether the other arm is `True`. -/
abbrev Pos := Nat × Name × Bool × Bool

structure PCand where
  ctors : Std.HashSet Name := {}
  fieldNames : Std.HashMap Name (Array Name) := {}
  packs : Std.HashMap Name (Array Pos) := {}
  lemParams : Std.HashMap Name (Array Pos) := {}
  consts : Std.HashSet Name := {}

structure WRow where
  lem : Name
  kind : String
  target : String
  callee : Name
  occ : Nat
  argIdx : Nat
  vcLeft : Bool
  otherTrue : Bool
  st : Stack
  args : Array Expr
  deriving Inhabited

structure W where
  rows : Array WRow := #[]
  occ : Std.HashMap String Nat := {}
  memo : Std.HashMap Expr Bool := {}
  nodes : Nat := 0
  apps : Nat := 0

partial def containsP (st : IO.Ref W) (cs : Std.HashSet Name) (e : Expr) : MetaM Bool := do
  match (← st.get).memo[e]? with
  | some b => return b
  | none =>
    let b ← match e with
      | .const n _ => pure (cs.contains n)
      | .app f a => do pure ((← containsP st cs f) || (← containsP st cs a))
      | .lam _ t b _ | .forallE _ t b _ => do pure ((← containsP st cs t) || (← containsP st cs b))
      | .letE _ t v b _ => do pure ((← containsP st cs t) || (← containsP st cs v) || (← containsP st cs b))
      | .mdata _ b | .proj _ _ b => containsP st cs b
      | _ => pure false
    st.modify fun s => { s with memo := s.memo.insert e b }
    return b

/-- How a match's alternative binders are labeled: by the discriminant of
    the same name, else by position when the alternative binds one variable
    per discriminant, else by the first discriminant that has a source. -/
def altLabeler (st : Stack) (discrs : Array Expr) : MetaM (Nat → Name → Option String) := do
  let mut info : Array (Option String × Option Name) := #[]
  for d in discrs do
    let nm := match d.consumeMData with
      | .bvar i => if i < st.size then some st[st.size - 1 - i]!.name else none
      | _ => none
    info := info.push (← sourceOf st d, nm)
  let first := info.findSome? (·.1)
  let n := info.size
  return fun pos name =>
    match info.find? (fun (_, nm) => nm == some name) with
    | some (s, _) => s <|> first
    | none => if n > 1 && pos < n then (info[pos]!.1 <|> first) else first

structure PCx where
  lem : Name
  st : Stack
  paramsLeft : Nat := 0
  door : Option (Name × Array Name × Nat) := none
  inherit : Option (Nat → Name → Option String) := none
  inheritPos : Nat := 0

/-- A binder whose type is data, not a hypothesis. -/
def isDataTy (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  match ty.getAppFn with
  | .const c _ => c == ``Nat || c == ``List || c == ``L4YAML.Surface.SurfPos || c == ``ScannerState || c == ``Char ||
      c == ``Bool || c == ``String || c == ``Option || c == ``Prod || c == ``Int || c == ``YamlContext
  | .sort _ => true
  | _ => (piConcl ty).isSort

/-- A `have`'s label: its name, its source, and — for a transport — the
    hypotheses the transport takes. -/
def letLabel (st : Stack) (n : Name) (v : Expr) : MetaM String := do
  let v' := peelSafe v
  let src ← sourceOf st v
  let inputs : Array String := match v'.getAppFn with
    | .const c _ => if c.getRoot == `L4YAML then v'.getAppArgs.filterMap (fun a =>
        match a.consumeMData with
        | .bvar i => if i < st.size then (if isDataTy st[st.size - 1 - i]!.ty then none else some (bname st[st.size - 1 - i]!.name)) else none
        | _ => none) else #[]
    | _ => #[]
  let tail := match src with
    | some s => if inputs.isEmpty then s!"<{s}" else s!"<{s}({String.intercalate "," inputs.toList})"
    | none => ""
  return s!"let:{bname n}{tail}"

partial def walkP (w : IO.Ref W) (cd : PCand) (cx : PCx) (e : Expr) : MetaM Unit := do
  w.modify fun s => { s with nodes := s.nodes + 1 }
  match e with
  | .mdata _ b => walkP w cd cx b
  | .lam n t b _ =>
    let mut prov : Option String := none
    let mut door := cx.door
    let mut pos := cx.inheritPos
    if cx.paramsLeft > 0 then prov := some s!"param:{short cx.lem}.{bname n}"
    else if let some (c, fields, i) := cx.door then
      if i < fields.size then
        prov := some s!"door:{short c}.{fields[i]!}"
        door := some (c, fields, i + 1)
      else door := none
    else if let some f := cx.inherit then
      prov := f pos n <|> some s!"λ:{bname n}"
      pos := pos + 1
    else prov := some s!"λ:{bname n}"
    let inherit' := if cx.paramsLeft > 0 then none else cx.inherit
    walkP w cd { cx with st := cx.st.push { name := n, ty := t, prov }, paramsLeft := cx.paramsLeft - 1, door, inherit := inherit', inheritPos := pos } b
  | .forallE n t b _ =>
    walkP w cd { cx with st := cx.st.push { name := n, ty := t, prov := none }, paramsLeft := 0, door := none, inherit := none } b
  | .letE n t v b _ =>
    let cx0 := { cx with paramsLeft := 0, door := none, inherit := none }
    walkP w cd cx0 v
    walkP w cd { cx0 with st := cx.st.push { name := n, ty := t, prov := some (← letLabel cx.st n v) } } b
  | .proj _ _ b => walkP w cd { cx with paramsLeft := 0, door := none, inherit := none } b
  | .app .. =>
    unless ← containsP w cd.consts e do return
    let f := e.getAppFn
    let args := e.getAppArgs
    let cx0 := { cx with paramsLeft := 0, door := none, inherit := none }
    match f with
    | .const n _ =>
      if let some (arity, k) := transparent n then
        if k < args.size then
          return ← walkP w cd cx (mkAppN args[k]! (args.extract arity args.size)).headBeta
      if n == ``letFun && args.size ≥ 4 then
        match args[3]! with
        | .lam bn bt bb _ =>
          walkP w cd cx0 args[2]!
          walkP w cd { cx0 with st := cx.st.push { name := bn, ty := bt, prov := some (← letLabel cx.st bn args[2]!) } } bb
        | g =>
          walkP w cd cx0 args[2]!
          walkP w cd cx0 g
        for a in args.extract 4 args.size do walkP w cd cx0 a
        return
      if n == ``PendingNode.casesOn then
        let env ← getEnv
        let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode"
        let majorPos := iv.numParams + 1 + iv.numIndices
        for i in [0:args.size] do
          if i > majorPos && i ≤ majorPos + iv.ctors.length then
            let c := iv.ctors[i - majorPos - 1]!
            walkP w cd { cx0 with door := some (c, cd.fieldNames.getD c #[], 0) } args[i]!
          else walkP w cd cx0 args[i]!
        return
      if let some (_, discrs, brs) ← branchesOf n args then
        let f ← altLabeler cx.st discrs
        for i in [0:args.size] do
          if brs.contains i then walkP w cd { cx0 with inherit := some f, inheritPos := 0 } args[i]!
          else walkP w cd cx0 args[i]!
        return
      if cd.ctors.contains n then
        let env ← getEnv
        let some (.ctorInfo cv) := env.find? n | throwError "{n}: not a constructor"
        let fieldArgs := args.extract cv.numParams args.size
        let producer := fieldArgs.any fun a => !(a.consumeMData.isBVar || a.consumeMData.isFVar)
        if producer && args.size == cv.numParams + cv.numFields then
          let key := s!"{cx.lem}/{n}"
          let occ := ((← w.get).occ.getD key 0) + 1
          w.modify fun s => { s with occ := s.occ.insert key occ, apps := s.apps + 1 }
          for (idx, field, vcLeft, otherTrue) in cd.packs.getD n #[] do
            w.modify fun s => { s with rows := s.rows.push { lem := cx.lem, kind := "ctor", target := s!"{short n}.{field}", callee := n, occ, argIdx := idx, vcLeft, otherTrue, st := cx.st, args } }
      if let some ps := cd.lemParams[n]? then
        let key := s!"{cx.lem}/{n}"
        let occ := ((← w.get).occ.getD key 0) + 1
        w.modify fun s => { s with occ := s.occ.insert key occ }
        for (idx, pname, vcLeft, otherTrue) in ps do
          if idx < args.size then
            w.modify fun s => { s with rows := s.rows.push { lem := cx.lem, kind := "param", target := s!"{short n}.{pname}", callee := n, occ, argIdx := idx, vcLeft, otherTrue, st := cx.st, args } }
      for a in args do walkP w cd cx0 a
    | _ =>
      walkP w cd cx0 f
      for a in args do walkP w cd cx0 a
  | _ => return

def walkTheoremP (w : IO.Ref W) (cd : PCand) (n : Name) : MetaM Unit := do
  let some ci := (← getEnv).find? n | return
  let some v := ci.value? (allowOpaque := true) | return
  w.modify fun s => { s with memo := {} }
  unless ← containsP w cd.consts v do return
  walkP w cd { lem := n, st := #[], paramsLeft := ci.type.getForallBinderNames.length } v

/-! ## §2 Classifying a pack argument, and the spend -/

/-- Push every leading lambda of `e`, labeled by `f`. -/
partial def enterAllF (st : Stack) (f : Nat → Name → Option String) (e : Expr) (pos : Nat := 0) : Stack × Expr :=
  match e.consumeMData with
  | .lam n t b _ => enterAllF (st.push { name := n, ty := t, prov := f pos n <|> some s!"λ:{bname n}" }) f b (pos + 1)
  | e => (st, e)

def isThmN (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.thmInfo _) => true | _ => false

def isCtorN (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.ctorInfo _) => true | _ => false

/-- A lambda whose body is a proposition: a predicate argument, not a proof. -/
partial def isPredLam (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ => isPredLam b
  | .forallE .. => true
  | .sort _ => true
  | b => match b.getAppFn with
    | .const c _ => c == ``And || c == ``Or || c == ``Exists || c == ``Not || c == ``Eq || c == ``True
    | _ => false

def bindOf (st : Stack) (e : Expr) : Option Bind :=
  match e.consumeMData with
  | .bvar i => if i < st.size then some st[st.size - 1 - i]! else none
  | _ => none

/-- The kind of hypothesis a spend or a relay bottoms in. -/
def bindKind (b : Option Bind) : String :=
  match b with
  | none => "other"
  | some b =>
    if vcOutside b.ty then "chain"
    else if hasHead b.ty resumeN then "frames"
    else if hasHead b.ty tailN then "tail"
    else if (piConcl b.ty).isAppOf streamN then "route"
    else "other"

/-- The closure a pack body spends for the value's end, read to its innermost
    hypothesis: the head chain as text, and the binder that hypothesis is. -/
partial def spendOf (env : Environment) (st : Stack) (e : Expr) (fuel : Nat := 10) : MetaM (String × Option Bind) := do
  if fuel == 0 then return ("…", none)
  let e := peelSafe e
  match e with
  | .lam n t b _ => spendOf env (st.push { name := n, ty := t, prov := none }) b fuel
  | .bvar _ =>
    let b := bindOf st e
    return (s!"{(b.map fun b => bname b.name).getD "#?"}←{(b.bind (·.prov)).getD "?"}", b)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .bvar _ =>
      let b := bindOf st f
      return (s!"{(b.map fun b => bname b.name).getD "#?"}←{(b.bind (·.prov)).getD "?"}", b)
    | .const c _ =>
      if let some (_, discrs, brs) ← branchesOf c args then
        let lab ← altLabeler st discrs
        let mut parts : Array String := #[]
        let mut bind : Option Bind := none
        for b in brs do
          let (st', body) := enterAllF st lab args[b]!
          let (s, bb) ← spendOf env st' body (fuel - 1)
          if s == "absurd" || s == "?" || s == "trivial" || s == "True.intro" then continue
          parts := parts.push s
          if bind.isNone then bind := bb
        if parts.isEmpty then return ("?", none)
        return (if parts.size == 1 then parts[0]! else "alt[" ++ String.intercalate "|" parts.toList ++ "]", bind)
      if deadEnd c then return ("absurd", none)
      if c == ``Or.inl || c == ``Or.inr || c == ``Exists.intro || c == ``And.intro then
        if args.size > 0 then return ← spendOf env st args[args.size - 1]! (fuel - 1)
        return (short c, none)
      if c.getRoot == `L4YAML && isThmN env c then
        for a in args do
          let a' := peelSafe a
          let cand := match a' with
            | .lam .. => !isPredLam a'
            | .bvar .. => (match bindOf st a' with | some b => bindKind (some b) != "other" | none => false)
            | .app .. => (match a'.getAppFn with
                | .bvar _ => true
                | .const m _ => m.getRoot == `L4YAML && isThmN env m
                | _ => false)
            | _ => false
          if cand then
            let (s, bb) ← spendOf env st a' (fuel - 1)
            if bb.isSome || s.startsWith "alt[" then return (s!"{short c}({s})", bb)
        return (short c, none)
      if c.getRoot == `L4YAML && isCtorN env c then return (s!"ctor:{short c}", none)
      return (short c, none)
    | _ => return ("?", none)
  | _ => return ("?", none)

structure PackRead where
  cls : String
  ns : String := "—"
  wits : Array (String × Bool) := #[]
  spend : String := "—"
  spendTail : Bool := false
  deriving Inhabited

/-- A paid pack's reading: the witnesses, then the closure's spend; a pack
    produced by a match is read branch by branch, its punt branches dropped. -/
partial def paidRead (env : Environment) (st : Stack) (x : Expr) (fuel : Nat := 8) : MetaM PackRead := do
  if fuel == 0 then return { cls := "other(fuel)" }
  let mut x := peelSafe x
  if let .const c _ := x.getAppFn then
    if let some (_, discrs, brs) ← branchesOf c x.getAppArgs then
      let lab ← altLabeler st discrs
      let mut out : Array PackRead := #[]
      for b in brs do
        let (st', body) := enterAllF st lab x.getAppArgs[b]!
        let r ← paidRead env st' body (fuel - 1)
        unless r.cls == "punt" || r.cls.startsWith "other(" do out := out.push r
      if out.isEmpty then return { cls := "punt" }
      if out.size == 1 then return out[0]!
      return { cls := "alt[" ++ String.intercalate "|" (out.map (·.cls)).toList ++ "]",
               ns := String.intercalate "|" (out.map (·.ns)).toList, wits := out.foldl (· ++ ·.wits) #[],
               spend := String.intercalate "|" (out.map (·.spend)).toList, spendTail := out.any (·.spendTail) }
    if c == ``Or.inr || c == ``Or.inl then
      -- a nested option inside the paid arm (a stamp-or-slot pair): its arm
      -- is read as it stands
      if x.getAppNumArgs ≥ 3 then return ← paidRead env st (x.getArg! 2) (fuel - 1)
  let mut wits : Array (String × Bool) := #[]
  let mut fuel2 := 8
  while fuel2 > 0 do
    fuel2 := fuel2 - 1
    let xf := x.getAppFn
    let xa := x.getAppArgs
    match xf with
    | .const ``Exists.intro _ =>
      if xa.size ≥ 4 then
        let α := xa[0]!.consumeMData
        if α.isConstOf ``Nat then wits := wits.push (ppc st xa[2]!, false)
        else if α.isAppOf ``List then wits := wits.push (ppc st xa[2]!, true)
        x := peelSafe xa[3]!
      else break
    | .const ``And.intro _ =>
      if xa.size ≥ 4 then x := peelSafe xa[3]! else break
    | _ => break
  let ns := if wits.isEmpty then "—" else String.intercalate "," (wits.map (·.1)).toList
  let lists := wits.filter (·.2)
  if !lists.isEmpty && lists.all (·.1 == "[]") && wits.all (·.2) then return { cls := "empty", ns, wits }
  if x.isConstOf ``trivial || x.isConstOf ``True.intro then return { cls := "punt" }
  let (spend, bind) ← spendOf env st x
  let kind := bindKind bind
  let spendTail := match bind with | some b => hasHead b.ty tailN | none => false
  return { cls := s!"paid:{kind}", ns, wits, spend, spendTail }

partial def packCls (env : Environment) (st : Stack) (e : Expr) (vcLeft otherTrue : Bool) (fuel : Nat := 24) : MetaM PackRead := do
  if fuel == 0 then return { cls := "other(fuel)" }
  let e := peelSafe e
  let relayOf (x : Expr) : MetaM PackRead := do
    let src ← sourceOf st x
    return { cls := s!"relay:{bindKind (bindOf st x)}({src.getD s!"?{pp st x}"})" }
  match e with
  | .bvar _ => relayOf e
  | .proj _ _ b => relayOf b
  | .lam .. =>
    if isPredLam e then return { cls := "other(predicate)" }
    -- a bare closure (a parameter with no option around it)
    let (spend, bind) ← spendOf env st e
    return { cls := s!"paid:{bindKind bind}", spend, spendTail := match bind with | some b => hasHead b.ty tailN | none => false }
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      if let some (_, discrs, brs) ← branchesOf n args then
        let lab ← altLabeler st discrs
        let mut out : Array PackRead := #[]
        for b in brs do
          let (st', body) := enterAllF st lab args[b]!
          out := out.push (← packCls env st' body vcLeft otherTrue (fuel - 1))
        -- a punt branch beside a paid one mirrors the source's own option
        let live := out.filter fun r => r.cls != "punt"
        if live.isEmpty then return { cls := "punt" }
        if live.size == 1 then return live[0]!
        return { cls := "alt[" ++ String.intercalate "|" (live.map (·.cls)).toList ++ "]",
                 ns := String.intercalate "|" (live.map (·.ns)).toList, wits := live.foldl (· ++ ·.wits) #[],
                 spend := String.intercalate "|" (live.map (·.spend)).toList, spendTail := live.any (·.spendTail) }
      if n == ``Or.inl && args.size ≥ 3 then
        if vcLeft then return ← paidRead env st args[2]! else return { cls := if otherTrue then "punt" else "stamp" }
      if n == ``Or.inr && args.size ≥ 3 then
        if !vcLeft then return ← paidRead env st args[2]! else return { cls := if otherTrue then "punt" else "stamp" }
      if (n == ``And.left || n == ``And.right) && args.size ≥ 3 then return ← relayOf args[2]!
      if (← getProjectionFnInfo? n).isSome && args.size ≥ 1 then return ← relayOf args[args.size - 1]!
      if n == ``Or.imp && args.size ≥ 7 then return { cls := s!"step({(← sourceOf st args[6]!).getD "?"})" }
      if (n == ``Or.imp_left || n == ``Or.imp_right) && args.size ≥ 5 then return { cls := s!"step({(← sourceOf st args[4]!).getD "?"})" }
      if n.getRoot == `L4YAML && isThmN env n then
        let mut inner : Array PackRead := #[]
        for a in args do
          let a' := peelSafe a
          let ok := match a' with
            | .lam .. => !isPredLam a'
            | .bvar .. => (match bindOf st a' with | some b => !isDataTy b.ty | none => false)
            | .app .. => (match a'.getAppFn with | .const m _ => !isCtorN env m | _ => true)
            | .proj .. => true
            | _ => false
          if ok then
            let r ← packCls env st a' vcLeft otherTrue (fuel - 1)
            unless r.cls.startsWith "other(" do inner := inner.push r
        let nss := inner.filterMap fun r => if r.ns == "—" then none else some r.ns
        let sps := inner.filterMap fun r => if r.spend == "—" then none else some r.spend
        return { cls := s!"via:{short n}[{String.intercalate ";" (inner.map (·.cls)).toList}]",
                 ns := if nss.isEmpty then "—" else String.intercalate "|" nss.toList,
                 wits := inner.foldl (· ++ ·.wits) #[],
                 spend := if sps.isEmpty then "—" else String.intercalate "|" sps.toList,
                 spendTail := inner.any (·.spendTail) }
      if x_isPaidCtor n then return ← paidRead env st e
      return { cls := s!"other({short2 n})" }
    | .bvar _ => relayOf f
    | _ => return { cls := "other(app)" }
  | _ => return { cls := "other(?)" }
where
  x_isPaidCtor (n : Name) : Bool := n == ``Exists.intro || n == ``And.intro

/-- The atoms of a written list (`a :: b :: []` → `[a, b]`, tail variable
    none; `nsU` → `[]`, variable `nsU`); a bare level is one atom. -/
def atomsOf (wits : Array (String × Bool)) (own : String) : List String × Option String := Id.run do
  let mut atoms : List String := []
  let mut var : Option String := none
  for (s, isList) in wits do
    unless isList do continue
    let parts := (s.splitOn " :: ").map (·.trimAscii.toString)
    match parts.getLast? with
    | some "[]" => atoms := atoms ++ parts.dropLast
    | some v => atoms := atoms ++ parts.dropLast; if var.isNone then var := some v
    | none => pure ()
  if atoms.isEmpty && var.isNone then
    match (wits.filter fun (_, l) => !l).back? with
    | some (s, _) => atoms := [s]
    | none => if own != "—" then atoms := [own]
  return (atoms.eraseDups, var)

/-- Which held shapes name a level of the written list. -/
def hits (holds : Array String) (atoms : List String) (var : Option String) : Array String := Id.run do
  let mut out : Array String := #[]
  for h in holds do
    let name := ((h.splitOn ":")[0]?).getD h
    let shape := (h.drop (name.length + 1)).toString
    let inner := if shape.startsWith "tail(" then Option.some (((shape.drop 5).toString.splitOn ")")[0]!)
      else if shape.startsWith "tailFact(" then some (((shape.drop 9).toString.splitOn ")")[0]!)
      else if shape.startsWith "frames(" then some (((shape.drop 7).toString.splitOn ")")[0]!)
      else none
    let some lv := inner | continue
    let hit := if shape.startsWith "frames(" then
        let parts := (lv.splitOn " :: ").map (·.trimAscii.toString)
        (match parts.head? with | some a => atoms.contains a | none => false) || (var.isSome && parts == [var.get!])
      else atoms.contains lv
    if hit then out := out.push name
  return out

/-! ## §3 The pins -/

def pinned : Bool := true
def expectedPacks : List String := [
  "pendingContent.h_vpack arm=l lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingProps.h_kslot arm=l lvl=∃ns∀nv∈ns premises=[SBlockNode(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingProps.h_kslotE arm=l lvl=∃ne∃nv(n=ne + 1) premises=[SBlockNode(n),SCompactSeqTail(ne),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingBlockContent.h_kslot arm=l lvl=∃nv premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingBlockContent.h_kslotUp arm=l lvl=∃ns∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingBlock.h_kslot arm=l lvl=∃nv premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingBlock.h_kslotUp arm=l lvl=∃ns∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingMapValue.h_ivl arm=r/stamp lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "pendingMapValue.h_vslot arm=l lvl=(sc.currentIndent≤n)(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "pendingMapValue.h_kslot arm=l lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "pendingMapValue.h_explUp arm=l lvl=∃sp_q∃ns(GLit('?'))∀nv∈ns premises=[SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no"]
def expectedFramesOn : List String := [
  "pendingContent.h_framesV frames(ks)@ExplValueLine(nv)←landing",
  "pendingProps.h_closeFV frames(ks)@ExplValueLine(nv)←SBlockNode(n)",
  "pendingProps.h_closeFEV frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)",
  "pendingBlockContent.h_closeFV frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)",
  "pendingBlock.h_closeFV frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)",
  "pendingMapValue.h_closeFV frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1)",
  "pendingMapValue.h_framesV frames(ks)@ExplValueLine(nv)←landing"]
def expectedParams : List String := [
  "accum_block_on_closeThenBlock.h_vpack arm=l lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_block_on_closeThenBlock.h_vslot arm=l lvl=∃nv∃sp_a(SLYamlStream(sp_start))(sc.currentIndent≤nv)(needIndentCheck(…)=false)(simpleKeyAllowed(…)=true)(sp_scan.col=nv + 1)(?)(Or)∃nsU∀nvU∈nsU premises=[SBlockIndented(nv),SIndent(nvU),GLit(':'),SBlockIndented(nvU)] ⊢ SLYamlStream tail=no",
  "accum_block_on_pendingBlock.h_kslot arm=l lvl=∃nv premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_block_on_pendingBlock.h_kslotUp arm=l lvl=∃ns∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_block_on_pendingBlockContent.h_kslot arm=l lvl=∃nv premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_block_on_pendingBlockContent.h_kslotUp arm=l lvl=∃ns∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_block_on_pendingContent.h_vpack arm=l lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_content_on_pendingBlock_indented.h_kslotUp_old arm=l lvl=∃ns∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_content_on_pendingBlock_indented.h_kslot_old arm=l lvl=∃nv premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_content_on_pendingMapValue_indented.h_ivl_mv arm=r/stamp lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "accum_content_on_pendingMapValue_indented.h_kslot arm=l lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "accum_content_on_pendingMapValue_indented.h_vslot arm=l lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "colon_open_map_explicit.hvp arm=l lvl= premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "colon_open_map_implicit.h_kslot arm=l lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "colon_open_map_props.h_kslot arm=l lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "entryChainMap.up arm=l lvl=∀nvX∈ns premises=[SBlockIndented(n),SCompactSeqTail(n)] ⊢ ExplValueLine(nvX) tail=no",
  "entryKeyPack_of_dispatch.h_compact arm=l lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "entryKeyPack_of_dispatch.h_ivl arm=r/stamp lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "entryKeyPack_of_dispatch.h_nodeV arm=l lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "entryPropsKeyPack_of_dispatch.h_compact arm=l lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "entryPropsKeyPack_of_dispatch.h_ivl arm=r/stamp lvl=(?)(sp_scan.col=n + 1)∃ns∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "entryPropsKeyPack_of_dispatch.h_nodeV arm=l lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "explFrameValueLine.h_kslot arm=l lvl=∃ns∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "flowKeyPack_of_close.h_key arm=l lvl=∃k∃sp_key(?)(?)(kc=k)(And)∃ns∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "flowKeyRoute_of_open.h_compact_pair arm=l lvl=∃nv0∃ns∀nv∈nv0 :: ns premises=[SBlockIndented(nc),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "flowVPack_of_close.h_vslot arm=l lvl=∃ns∀nv∈ns premises=[SFlowContent(n),SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "indicator_open_map.h_explUp_chain arm=l lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "question_open_map.h_explUp_chain arm=l lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ SLYamlStream tail=no",
  "slotChainMap.up arm=l lvl=∀nvX∈ns premises=[SBlockIndented(nv)] ⊢ ExplValueLine(nvX) tail=no"]
def expectedWriters : List String := [
  "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslot idx=k := paid:chain ns=nv spend=hkv←param:accum_block_on_closeThenBlock.h_vslot holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_seqBottom:frames([])←SCompactSeqTail(k); h_seqFrames:frames(ks)←SCompactSeqTail(k); h_seqFramesV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ held(h_valF)",
  "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslotUp idx=k := paid:chain ns=nsU spend=hkvU←param:accum_block_on_closeThenBlock.h_vslot holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_seqBottom:frames([])←SCompactSeqTail(k); h_seqFrames:frames(ks)←SCompactSeqTail(k); h_seqFramesV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
  "accum_block_on_closeThenBlock #1 param:indicator_open_map.h_explUp_chain idx=— := alt[paid:chain|paid:chain|paid:chain] ns=nv :: nsU|nv :: []|nsU spend=slotChainMap(alt[kv←param:accum_block_on_closeThenBlock.h_vslot|kvU←param:accum_block_on_closeThenBlock.h_vslot])|slotChainMap(kv←param:accum_block_on_closeThenBlock.h_vslot)|slotChainMap(kvU←param:accum_block_on_closeThenBlock.h_vslot) holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ held(h_valF)",
  "accum_block_on_closeThenBlock #1 param:slotChainMap.up idx=— := paid:chain ns=— spend=alt[kv←param:accum_block_on_closeThenBlock.h_vslot|kvU←param:accum_block_on_closeThenBlock.h_vslot] holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ level-var",
  "accum_block_on_closeThenBlock #2 param:slotChainMap.up idx=— := paid:chain ns=— spend=kv←param:accum_block_on_closeThenBlock.h_vslot holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ level-var",
  "accum_block_on_closeThenBlock #3 param:slotChainMap.up idx=— := relay:chain(param:accum_block_on_closeThenBlock.h_vslot) ns=— spend=— holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ —",
  "accum_block_on_closeThenBlock #1 param:colon_open_map_explicit.hvp idx=— := relay:chain(λ:hvp) ns=— spend=— holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ —",
  "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslot idx=nv + 1 + m := paid:chain ns=nv spend=kv←param:accum_block_on_closeThenBlock.h_vslot holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1)] ⊢ held(h_valF)",
  "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslotUp idx=nv + 1 + m := paid:chain ns=nsU spend=kvU←param:accum_block_on_closeThenBlock.h_vslot holds=[h_valF:frames(nv :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1)] ⊢ level-var",
  "accum_block_on_noPending #1 ctor:pendingBlock.h_kslot idx=k := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_on_noPending #1 ctor:pendingBlock.h_kslotUp idx=k := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_on_noPending #1 param:indicator_open_map.h_explUp_chain idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslot idx=k := paid:chain ns=nv spend=kslot←param:accum_block_on_pendingBlock.h_kslot holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslotUp idx=k := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlock.h_kslotUp holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslot idx=k := paid:chain ns=nv spend=kslot←param:accum_block_on_pendingBlock.h_kslot holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslotUp idx=k := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlock.h_kslotUp holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
  "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
  "accum_block_on_pendingBlock #1 param:indicator_open_map.h_explUp_chain idx=— := alt[paid:chain|paid:chain|paid:chain] ns=nv :: nsU|nv :: []|nsU spend=entryChainMap(frameChainCons(kslot←param:accum_block_on_pendingBlock.h_kslotUp))|entryChainMap(frameChainOne(kslot←param:accum_block_on_pendingBlock.h_kslotUp))|entryChainMap(kslotU←param:accum_block_on_pendingBlock.h_kslot) holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_block_on_pendingBlock #1 param:entryChainMap.up idx=— := via:frameChainCons[relay:chain(param:accum_block_on_pendingBlock.h_kslotUp);relay:chain(param:accum_block_on_pendingBlock.h_kslot)] ns=— spend=— holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingBlock #2 param:entryChainMap.up idx=— := via:frameChainOne[relay:chain(param:accum_block_on_pendingBlock.h_kslotUp)] ns=— spend=— holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingBlock #3 param:entryChainMap.up idx=— := relay:chain(param:accum_block_on_pendingBlock.h_kslot) ns=— spend=— holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
  "accum_block_on_pendingBlock #1 param:colon_open_map_explicit.hvp idx=— := paid:chain ns=— spend=kslot←λ:kslot holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslot idx=n + 1 + m := paid:chain ns=nv spend=kslot←param:accum_block_on_pendingBlock.h_kslot holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslotUp idx=n + 1 + m := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlock.h_kslotUp holds=[h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslot idx=k := paid:chain ns=nv spend=kslot←param:accum_block_on_pendingBlockContent.h_kslot holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslotUp idx=k := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlockContent.h_kslotUp holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
  "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
  "accum_block_on_pendingBlockContent #1 param:indicator_open_map.h_explUp_chain idx=— := punt ns=— spend=— holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
  "accum_block_on_pendingBlockContent #1 param:colon_open_map_explicit.hvp idx=— := paid:chain ns=— spend=kslot←λ:kslot holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := relay:chain(param:accum_block_on_pendingContent.h_vpack) ns=— spend=— holds=[h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ —",
  "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ —",
  "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ —",
  "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_pendingContent.h_vpack idx=— := relay:chain(door:pendingContent.h_vpack) ns=— spend=— holds=[h_framesS109:frames(ks)←landing; h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(kk)←landing] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV✝:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ level-var",
  "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV✝:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
  "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV✝:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
  "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV✝:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
  "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslot idx=— := relay:chain(door:pendingBlockContent.h_kslot) ns=— spend=— holds=[h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslotUp idx=— := relay:chain(door:pendingBlockContent.h_kslotUp) ns=— spend=— holds=[h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslot idx=— := relay:chain(door:pendingBlock.h_kslot) ns=— spend=— holds=[h_closeF✝:frames(ks)←SCompactSeqTail(n_old); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
  "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslotUp idx=— := relay:chain(door:pendingBlock.h_kslotUp) ns=— spend=— holds=[h_closeF✝:frames(ks)←SCompactSeqTail(n_old); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
  "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingMapValue.h_kslot holds=[h_closeF155:frames(nmv :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1)] ⊢ level-var",
  "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vslot idx=— := punt ns=— spend=— holds=[h_closeF155:frames(nmv :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1)] ⊢ —",
  "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vpack idx=— := via:frameChainUnion[via:frameChainUnion[paid:route;paid:chain];paid:chain] ns=nmv :: []|ns|nsU spend=frameChainOne(route←door:pendingMapValue.h_expl)|kslot←door:pendingMapValue.h_kslot|up←door:pendingMapValue.h_explUp holds=[h_closeF155:frames(nmv :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1)] ⊢ held(h_closeF155,h_seqF✝)",
  "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vslot idx=— := paid:chain ns=nmv spend=up←door:pendingMapValue.h_explUp holds=[h_closeF155:frames(nmv :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1)] ⊢ held(h_closeF155,h_seqF✝)",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslot idx=n := paid:chain ns=nv spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslotUp idx=n := paid:chain ns=ns spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslotUp_old holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_nodeV idx=— := paid:chain ns=nv :: [] spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_compact idx=— := paid:chain ns=— spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_ivl idx=— := paid:chain ns=— spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslot idx=n + 1 := paid:chain ns=nv :: [] spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslotE idx=n + 1 := paid:chain ns=n,nv spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV idx=— := paid:chain ns=nv :: [] spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact idx=— := paid:chain ns=— spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl idx=— := paid:chain ns=— spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslot idx=n := paid:chain ns=nv spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslotUp idx=n := paid:chain ns=ns spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslotUp_old holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslot idx=n := paid:chain ns=nv spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslotUp idx=n := paid:chain ns=ns spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslotUp_old holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_nodeV idx=— := paid:chain ns=nv :: [] spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_compact idx=— := paid:chain ns=— spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_ivl idx=— := paid:chain ns=— spend=frameChainOne(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_vpack idx=— := via:frameChainUnion[paid:route;paid:chain] ns=n :: []|ns spend=frameChainOne(route←param:accum_content_on_pendingMapValue_indented.h_expl)|kslot←param:accum_content_on_pendingMapValue_indented.h_kslot holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ held(h_closeF99,h_seqF168)",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_nodeV idx=— := via:explFrameValueLine[relay:other(param:accum_content_on_pendingMapValue_indented.h_expl);relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot)] ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ level-var",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_compact idx=— := relay:chain(let:h_compact_vslot<param:accum_content_on_pendingMapValue_indented.h_vslot(h_vslot)) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_ivl idx=— := relay:chain(let:h_ivl_pack<param:accum_content_on_pendingMapValue_indented.h_ivl_mv(h_ivl_mv)) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #1 param:explFrameValueLine.h_kslot idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslot idx=n + 1 := via:explFrameValueLine[relay:other(param:accum_content_on_pendingMapValue_indented.h_expl);relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot)] ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ none",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslotE idx=n + 1 := punt ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV idx=— := via:explFrameValueLine[relay:other(param:accum_content_on_pendingMapValue_indented.h_expl);relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot)] ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ level-var",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact idx=— := relay:chain(let:h_compact_vslot<param:accum_content_on_pendingMapValue_indented.h_vslot(h_vslot)) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl idx=— := relay:chain(let:h_ivl_pack<param:accum_content_on_pendingMapValue_indented.h_ivl_mv(h_ivl_mv)) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #2 param:explFrameValueLine.h_kslot idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #3 param:explFrameValueLine.h_kslot idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_vpack idx=— := via:frameChainUnion[paid:route;paid:chain] ns=n :: []|ns spend=frameChainOne(route←param:accum_content_on_pendingMapValue_indented.h_expl)|kslot←param:accum_content_on_pendingMapValue_indented.h_kslot holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ held(h_closeF99,h_seqF168)",
  "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_vpack idx=— := via:frameChainUnion[paid:route;paid:chain] ns=n :: []|ns spend=frameChainOne(route←param:accum_content_on_pendingMapValue_indented.h_expl)|kslot←param:accum_content_on_pendingMapValue_indented.h_kslot holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ held(h_closeF99,h_seqF168)",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_nodeV idx=— := via:explFrameValueLine[relay:other(param:accum_content_on_pendingMapValue_indented.h_expl);relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot)] ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ level-var",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_compact idx=— := relay:chain(let:h_compact_vslot<param:accum_content_on_pendingMapValue_indented.h_vslot(h_vslot)) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_ivl idx=— := relay:chain(let:h_ivl_pack<param:accum_content_on_pendingMapValue_indented.h_ivl_mv(h_ivl_mv)) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_on_pendingMapValue_indented #4 param:explFrameValueLine.h_kslot idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_closeF99:frames(n :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1)] ⊢ —",
  "accum_content_pending #1 ctor:pendingProps.h_kslot idx=n := relay:chain(door:pendingProps.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
  "accum_content_pending #1 ctor:pendingProps.h_kslotE idx=n := relay:chain(door:pendingProps.h_kslotE) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
  "accum_content_pending #2 ctor:pendingProps.h_kslot idx=n := relay:chain(door:pendingProps.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
  "accum_content_pending #2 ctor:pendingProps.h_kslotE idx=n := relay:chain(door:pendingProps.h_kslotE) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
  "accum_content_pending #1 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(0); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(0); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ level-var",
  "accum_content_pending #2 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(0); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(0); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ level-var",
  "accum_content_pending #1 ctor:pendingBlockContent.h_kslot idx=k := paid:chain ns=nv spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ none",
  "accum_content_pending #1 ctor:pendingBlockContent.h_kslotUp idx=k := punt ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ —",
  "accum_content_pending #3 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
  "accum_content_pending #2 ctor:pendingBlockContent.h_kslot idx=k := paid:chain ns=nv spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ none",
  "accum_content_pending #2 ctor:pendingBlockContent.h_kslotUp idx=k := punt ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ —",
  "accum_content_pending #4 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
  "accum_content_pending #3 ctor:pendingBlockContent.h_kslot idx=k := paid:chain ns=nv spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ none",
  "accum_content_pending #3 ctor:pendingBlockContent.h_kslotUp idx=k := punt ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ —",
  "accum_content_pending #5 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
  "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslot_old idx=— := relay:chain(door:pendingBlock.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
  "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslotUp_old idx=— := relay:chain(door:pendingBlock.h_kslotUp) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_vslot idx=— := step(door:pendingMapValue.h_vslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeF99:frames(n_old :: ks)←SBlockNode(n_old + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n_old)←SBlockNode(n_old + 1)] ⊢ —",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_kslot idx=— := relay:chain(door:pendingMapValue.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeF99:frames(n_old :: ks)←SBlockNode(n_old + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n_old)←SBlockNode(n_old + 1)] ⊢ —",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_ivl_mv idx=— := relay:chain(door:pendingMapValue.h_ivl) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_closeF99:frames(n_old :: ks)←SBlockNode(n_old + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n_old)←SBlockNode(n_old + 1)] ⊢ —",
  "accum_flow_open_depth0 #1 param:flowKeyRoute_of_open.h_compact_pair idx=— := punt ns=— spend=— holds=[main:frames(ks)←landing] ⊢ —",
  "accum_flow_open_depth0 #2 param:flowKeyRoute_of_open.h_compact_pair idx=— := paid:chain ns=nv,[] spend=frameChainOne(kslot←door:pendingBlock.h_kslot) holds=[main:frames(ks)←landing; h_closeF✝:frames(ks)←SCompactSeqTail(n_old); h_closeFV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ none",
  "accum_flow_open_depth0 #3 param:flowKeyRoute_of_open.h_compact_pair idx=— := paid:route ns=n_old,[] spend=frameChainOne(route←door:pendingMapValue.h_expl) holds=[main:frames(ks)←landing; h_closeF✝:frames(n_old :: ks)←SBlockNode(n_old + 1); h_frames✝:frames(ks)←landing; h_closeFV✝:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV✝:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(n_old)←SBlockNode(n_old + 1)] ⊢ held(h_closeF✝,h_seqF✝)",
  "accum_step_flow #1 ctor:pendingContent.h_vpack idx=— := via:flowVPack_of_close[relay:other(let:h_tuple<let:h_gap(tl,h_gap))] ns=— spend=— holds=[] ⊢ level-var",
  "accum_step_flow #1 param:flowKeyPack_of_close.h_key idx=— := relay:other(let:h_tuple<let:h_gap(tl,h_gap)) ns=— spend=— holds=[] ⊢ —",
  "accum_step_flow #1 param:flowVPack_of_close.h_vslot idx=— := relay:other(let:h_tuple<let:h_gap(tl,h_gap)) ns=— spend=— holds=[] ⊢ —",
  "accum_step_flow #2 ctor:pendingContent.h_vpack idx=— := via:flowVPack_of_close[relay:other(let:h_tuple<let:h_gap(tl,h_gap))] ns=— spend=— holds=[] ⊢ level-var",
  "accum_step_flow #2 param:flowKeyPack_of_close.h_key idx=— := relay:other(let:h_tuple<let:h_gap(tl,h_gap)) ns=— spend=— holds=[] ⊢ —",
  "accum_step_flow #2 param:flowVPack_of_close.h_vslot idx=— := relay:other(let:h_tuple<let:h_gap(tl,h_gap)) ns=— spend=— holds=[] ⊢ —",
  "colon_fires_implicit_key #1 param:colon_open_map_implicit.h_kslot idx=— := relay:chain(param:colon_fires_implicit_key.h_key) ns=— spend=— holds=[h✝:tail(k)←SBlockMapEntry(k); h✝:tail(k)←SBlockMapEntry(k); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_kslot_pk:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_rfr_pk:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_rfrV_pk:tail(k)←SBlockMapEntry(k); h_rseq_pk:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_fires_props_key #1 param:colon_open_map_props.h_kslot idx=— := relay:chain(param:colon_fires_props_key.h_key) ns=— spend=— holds=[left✝:tail(k)←SBlockMapEntry(k); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_kslot_pk:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_resF_pk:tail(k)←SBlockMapEntry(k); h_resFV_pk:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_ivl idx=k := stamp ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_vslot idx=k := punt ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_kslot idx=k := paid:frames ns=nv :: [] spend=frameChainOne(resumeFrameRoute(contV←param:colon_open_map.h_resV_land))⊣tail holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ none",
  "colon_open_map #1 ctor:pendingMapValue.h_explUp idx=k := punt ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_ivl idx=nv := paid:chain ns=— spend=h_slot←let:h_slot holds=[] ⊢ none",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_vslot idx=nv := paid:chain ns=— spend=h_slot←let:h_slot holds=[] ⊢ none",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_kslot idx=nv := punt ns=— spend=— holds=[] ⊢ —",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_explUp idx=nv := punt ns=— spend=— holds=[] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_ivl idx=k := stamp ns=— spend=— holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_vslot idx=k := punt ns=— spend=— holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_kslot idx=k := paid:chain ns=ns spend=kslot←param:colon_open_map_implicit.h_kslot⊣tail holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k)] ⊢ level-var",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_explUp idx=k := punt ns=— spend=— holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_ivl idx=k := stamp ns=— spend=— holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_vslot idx=k := punt ns=— spend=— holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_kslot idx=k := paid:chain ns=ns spend=kslot←param:colon_open_map_props.h_kslot⊣tail holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k)] ⊢ level-var",
  "colon_open_map_props #1 ctor:pendingMapValue.h_explUp idx=k := punt ns=— spend=— holds=[h_kslot:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "compact_open_map #1 ctor:pendingMapValue.h_ivl idx=n + 1 + m := relay:other(?right(…)) ns=— spend=— holds=[] ⊢ —",
  "compact_open_map #1 ctor:pendingMapValue.h_vslot idx=n + 1 + m := relay:chain(let:h_vslot105<param:compact_open_map.hc(hc)) ns=— spend=— holds=[] ⊢ —",
  "compact_open_map #1 ctor:pendingMapValue.h_kslot idx=n + 1 + m := punt ns=— spend=— holds=[] ⊢ —",
  "compact_open_map #1 ctor:pendingMapValue.h_explUp idx=n + 1 + m := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingProps.h_kslot idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingProps.h_kslotE idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingProps.h_kslot idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingProps.h_kslotE idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingContent.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingContent.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "indicator_open_map #1 param:question_open_map.h_explUp_chain idx=— := relay:chain(param:indicator_open_map.h_explUp_chain) ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ —",
  "question_open_map #1 ctor:pendingMapValue.h_ivl idx=k := paid:route ns=— spend=h_route51←let:h_route51<param:question_open_map.h_res_land(h_res_land,h_sfx_land,h_nodoc_land,h_mk_land,h_pr_land) holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF)",
  "question_open_map #1 ctor:pendingMapValue.h_vslot idx=k := paid:route ns=— spend=h_route51←let:h_route51<param:question_open_map.h_res_land(h_res_land,h_sfx_land,h_nodoc_land,h_mk_land,h_pr_land) holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF)",
  "question_open_map #1 ctor:pendingMapValue.h_kslot idx=k := paid:chain ns=nsU spend=up←let:h_upAll<ret:frameChainUnion(h_explUp_chain) holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ level-var",
  "question_open_map #1 ctor:pendingMapValue.h_explUp idx=k := paid:chain ns=ns spend=up←let:h_upAll<ret:frameChainUnion(h_explUp_chain) holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ level-var"]
def expectedPerPos : List String := [
  "ctor:pendingContent.h_vpack writers=12 punt=2 stamp=0 empty=0 relay=0 step=0 via=5 chain=5 route=0 frames=0 tail=0 other=0 alt=0 held=3 levelVar=7 none=0 touched=10",
  "ctor:pendingProps.h_kslot writers=6 punt=2 stamp=0 empty=0 relay=2 step=0 via=1 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=2 touched=4",
  "ctor:pendingProps.h_kslotE writers=6 punt=3 stamp=0 empty=0 relay=2 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=1 touched=3",
  "ctor:pendingBlockContent.h_kslot writers=6 punt=0 stamp=0 empty=0 relay=0 step=0 via=0 chain=6 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=6 touched=6",
  "ctor:pendingBlockContent.h_kslotUp writers=6 punt=3 stamp=0 empty=0 relay=0 step=0 via=0 chain=3 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=3 none=0 touched=3",
  "ctor:pendingBlock.h_kslot writers=7 punt=1 stamp=0 empty=0 relay=0 step=0 via=0 chain=6 route=0 frames=0 tail=0 other=0 alt=0 held=2 levelVar=0 none=4 touched=6",
  "ctor:pendingBlock.h_kslotUp writers=7 punt=1 stamp=0 empty=0 relay=0 step=0 via=0 chain=6 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=6 none=0 touched=6",
  "ctor:pendingMapValue.h_ivl writers=6 punt=0 stamp=3 empty=0 relay=1 step=0 via=0 chain=1 route=1 frames=0 tail=0 other=0 alt=0 held=1 levelVar=0 none=1 touched=6",
  "ctor:pendingMapValue.h_vslot writers=6 punt=3 stamp=0 empty=0 relay=1 step=0 via=0 chain=1 route=1 frames=0 tail=0 other=0 alt=0 held=1 levelVar=0 none=1 touched=3",
  "ctor:pendingMapValue.h_kslot writers=6 punt=2 stamp=0 empty=0 relay=0 step=0 via=0 chain=3 route=0 frames=1 tail=0 other=0 alt=0 held=0 levelVar=3 none=1 touched=4",
  "ctor:pendingMapValue.h_explUp writers=6 punt=5 stamp=0 empty=0 relay=0 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=0 touched=1",
  "param:accum_block_on_closeThenBlock.h_vpack writers=11 punt=7 stamp=0 empty=0 relay=1 step=0 via=1 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=1 levelVar=2 none=0 touched=4",
  "param:accum_block_on_closeThenBlock.h_vslot writers=11 punt=10 stamp=0 empty=0 relay=0 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=1 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingBlock.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingBlock.h_kslotUp writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingBlockContent.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingBlockContent.h_kslotUp writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingContent.h_vpack writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingBlock_indented.h_kslotUp_old writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingBlock_indented.h_kslot_old writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingMapValue_indented.h_ivl_mv writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingMapValue_indented.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingMapValue_indented.h_vslot writers=1 punt=0 stamp=0 empty=0 relay=0 step=1 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:colon_open_map_explicit.hvp writers=3 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=3",
  "param:colon_open_map_implicit.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:colon_open_map_props.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:entryChainMap.up writers=3 punt=0 stamp=0 empty=0 relay=1 step=0 via=2 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=3",
  "param:entryKeyPack_of_dispatch.h_compact writers=4 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=4",
  "param:entryKeyPack_of_dispatch.h_ivl writers=4 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=4",
  "param:entryKeyPack_of_dispatch.h_nodeV writers=4 punt=0 stamp=0 empty=0 relay=0 step=0 via=2 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=2 touched=4",
  "param:entryPropsKeyPack_of_dispatch.h_compact writers=2 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=0 touched=2",
  "param:entryPropsKeyPack_of_dispatch.h_ivl writers=2 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=0 touched=2",
  "param:entryPropsKeyPack_of_dispatch.h_nodeV writers=2 punt=0 stamp=0 empty=0 relay=0 step=0 via=1 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=1 touched=2",
  "param:explFrameValueLine.h_kslot writers=4 punt=0 stamp=0 empty=0 relay=4 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=4",
  "param:flowKeyPack_of_close.h_key writers=2 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=2",
  "param:flowKeyRoute_of_open.h_compact_pair writers=3 punt=1 stamp=0 empty=0 relay=0 step=0 via=0 chain=1 route=1 frames=0 tail=0 other=0 alt=0 held=1 levelVar=0 none=1 touched=2",
  "param:flowVPack_of_close.h_vslot writers=2 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=2",
  "param:indicator_open_map.h_explUp_chain writers=4 punt=2 stamp=0 empty=0 relay=0 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=2 held=1 levelVar=0 none=1 touched=2",
  "param:question_open_map.h_explUp_chain writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:slotChainMap.up writers=3 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=3"]
def expectedLine : String :=
  "packs=11 framesOn=7 params=29 paramLemmas=19 apps=50 rows=151 ctorRows=74 paramRows=77 punt=42 stamp=3 empty=0 relay=36 step=1 via=12 chain=51 route=3 frames=1 tail=0 other=0 alt=2 held=11 levelVar=37 none=21 spendTail=3 lemmas=21 helpers=[explFrameValueLine,flowVPack_of_close,frameChainCons,frameChainOne,frameChainUnion] touched=109 nodes=12262"

/-! ## §4 The reading -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let mut cd : PCand := {}
  let mut packLines : Array String := #[]
  let mut framesLines : Array String := #[]
  let mut packKeys : Array String := #[]
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
          if vcOutside t then
            let (vcLeft, otherTrue) := sideOf t
            packs := packs.push (i, n, vcLeft, otherTrue)
            let (st', cl, lvl) := peelToClosure stk t #[]
            let (prems, concl, tail) := premisesOf env st' cl #[] false false
            packLines := packLines.push s!"  {short c}.{n} arm={if vcLeft then "l" else "r"}{if otherTrue then "" else "/stamp"} lvl={String.intercalate "" lvl.toList} premises=[{String.intercalate "," prems.toList}] ⊢ {concl} tail={if tail then "yes" else "no"}"
            packKeys := packKeys.push s!"{short c}.{n}"
          else if framesOnVC t then
            framesLines := framesLines.push s!"  {short c}.{n} {(holdShape env stk t none).getD "?"}"
        stk := stk.push { name := n, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    cd := { cd with ctors := cd.ctors.insert c, fieldNames := cd.fieldNames.insert c names, packs := cd.packs.insert c packs, consts := cd.consts.insert c }
  cd := { cd with consts := cd.consts.insert ``PendingNode.casesOn }
  -- the pack parameters: every theorem binder of the shape
  let mut thms : Array Name := #[]
  let mut paramLines : Array String := #[]
  let mut paramKeys : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML then continue
    unless ci matches .thmInfo _ do continue
    thms := thms.push n
    let mut ty := ci.type
    let mut i := 0
    let mut stk : Stack := #[]
    let mut ps : Array Pos := #[]
    while true do
      match ty with
      | .forallE pn t b _ =>
        if vcOutside t then
          let (vcLeft, otherTrue) := sideOf t
          ps := ps.push (i, pn, vcLeft, otherTrue)
          let (st', cl, lvl) := peelToClosure stk t #[]
          let (prems, concl, tail) := premisesOf env st' cl #[] false false
          paramLines := paramLines.push s!"  {short n}.{pn} arm={if vcLeft then "l" else "r"}{if otherTrue then "" else "/stamp"} lvl={String.intercalate "" lvl.toList} premises=[{String.intercalate "," prems.toList}] ⊢ {concl} tail={if tail then "yes" else "no"}"
          paramKeys := paramKeys.push s!"{short n}.{pn}"
        stk := stk.push { name := pn, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    if !ps.isEmpty then cd := { cd with lemParams := cd.lemParams.insert n ps, consts := cd.consts.insert n }
  paramLines := paramLines.qsort (· < ·)
  let w ← IO.mkRef ({} : W)
  for n in sorted thms do walkTheoremP w cd n
  let ws ← w.get
  -- the rows
  let mut writerLines : Array String := #[]
  let mut per : Std.HashMap String (Array String) := {}
  let mut lemmas : Std.HashSet Name := {}
  let mut helpers : Std.HashSet String := {}
  let mut cnt : Std.HashMap String Nat := {}
  let bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat := m.insert k (m.getD k 0 + 1)
  for r in ws.rows do
    unless r.argIdx < r.args.size do throwError "{r.target}: {r.args.size} args"
    -- the constructor's own level, where it has one
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
    let pr ← packCls env r.st r.args[r.argIdx]! r.vcLeft r.otherTrue
    let holds := holdsOf env r.st
    let clsHead := ((pr.cls.splitOn "(")[0]?).getD pr.cls
    let clsTag := if clsHead.startsWith "paid:" then clsHead
      else if clsHead.startsWith "via:" then "via"
      else if clsHead.startsWith "alt[" then "alt"
      else if clsHead.startsWith "relay:" then "relay"
      else if clsHead.startsWith "step" then "step"
      else if clsHead.startsWith "other" then "other" else clsHead
    lemmas := lemmas.insert r.lem
    if clsHead.startsWith "via:" then helpers := helpers.insert ((((clsHead.drop 4).toString).splitOn "[")[0]!)
    let verdict :=
      if clsHead.startsWith "paid:" || clsTag == "alt" || clsTag == "via" then
        let (atoms, var) := atomsOf pr.wits own
        let hs := hits holds atoms var
        if !hs.isEmpty then s!"held({String.intercalate "," hs.toList})"
        else if atoms.isEmpty then "level-var" else "none"
      else "—"
    let vTag := ((verdict.splitOn "(")[0]?).getD verdict
    cnt := bump cnt clsTag
    cnt := bump cnt s!"v:{vTag}"
    cnt := bump cnt s!"k:{r.kind}"
    if pr.spendTail then cnt := bump cnt "spendTail"
    per := per.insert r.target ((per.getD r.target #[]).push s!"{clsTag} {vTag}")
    writerLines := writerLines.push s!"  {short r.lem} #{r.occ} {r.kind}:{r.target} idx={own} := {pr.cls} ns={pr.ns} spend={pr.spend}{if pr.spendTail then "⊣tail" else ""} holds=[{String.intercalate "; " holds.toList}] ⊢ {verdict}"
  -- per position
  let mut perLines : Array String := #[]
  for (kind, ks) in [("ctor", packKeys), ("param", paramKeys.qsort (· < ·))] do
    for k in ks do
      let xs := per.getD k #[]
      let c (p : String) := (xs.filter fun s => (s.splitOn " ")[0]! == p).size
      let v (p : String) := (xs.filter fun s => (s.splitOn " ")[1]! == p).size
      let touched := xs.size - c "punt"
      perLines := perLines.push s!"  {kind}:{k} writers={xs.size} punt={c "punt"} stamp={c "stamp"} empty={c "empty"} relay={c "relay"} step={c "step"} via={c "via"} chain={c "paid:chain"} route={c "paid:route"} frames={c "paid:frames"} tail={c "paid:tail"} other={c "paid:other"} alt={c "alt"} held={v "held"} levelVar={v "level-var"} none={v "none"} touched={touched}"
  let g (k : String) := cnt.getD k 0
  let touched := ws.rows.size - g "punt"
  let helperL := (helpers.toArray.qsort (· < ·)).toList
  let paramLemmas := (cd.lemParams.toList.map (·.1)).length
  let line := s!"packs={packKeys.size} framesOn={framesLines.size} params={paramKeys.size} paramLemmas={paramLemmas} apps={ws.apps} rows={ws.rows.size} ctorRows={g "k:ctor"} paramRows={g "k:param"} punt={g "punt"} stamp={g "stamp"} empty={g "empty"} relay={g "relay"} step={g "step"} via={g "via"} chain={g "paid:chain"} route={g "paid:route"} frames={g "paid:frames"} tail={g "paid:tail"} other={g "paid:other"} alt={g "alt"} held={g "v:held"} levelVar={g "v:level-var"} none={g "v:none"} spendTail={g "spendTail"} lemmas={lemmas.size} helpers=[{String.intercalate "," helperL}] touched={touched} nodes={ws.nodes}"
  logInfo s!"ValueLinePacks {line}"
  logInfo s!"packs:\n{String.intercalate "\n" packLines.toList}"
  logInfo s!"framesOn:\n{String.intercalate "\n" framesLines.toList}"
  logInfo s!"params:\n{String.intercalate "\n" paramLines.toList}"
  logInfo s!"writers:\n{String.intercalate "\n" writerLines.toList}"
  logInfo s!"perPos:\n{String.intercalate "\n" perLines.toList}"
  unless packKeys.size == 11 do throwError "the packs moved under this pass: packs={packKeys.size}"
  unless pinned do return
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedPacks" packLines expectedPacks
  check "expectedFramesOn" framesLines expectedFramesOn
  check "expectedParams" paramLines expectedParams
  check "expectedWriters" writerLines expectedWriters
  check "expectedPerPos" perLines expectedPerPos
  unless line == expectedLine do
    throwError "ValueLinePacks moved:\n  got      {line}\n  expected {expectedLine}"

end Tests.Guards.ValueLinePacks
