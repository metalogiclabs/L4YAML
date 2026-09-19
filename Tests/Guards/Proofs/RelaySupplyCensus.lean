import L4YAML.Proofs.Production.StreamAccum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The census over RELAYS (DOCS item 212)

Four censuses stand before this one, and all four count TERMS: over the pending
park's CONSTRUCTORS (item 198), over their APPLICATION SITES (200), over lemma
CONCLUSIONS (201), and over the conclusions' own key (202).  Items 199, 201 and
211 each recorded the same gap, in the same words:

> A conjunct **relayed** with `Or.imp`, or discharged by passing a lemma whose
> own conclusion is the `∨ True`, writes no literal `Or.inl` or `Or.inr` and
> reads `inl=0 inr=0` — neither paid nor punted.  **A relay is invisible to
> anything that counts terms**, because it writes the answer down once and the
> writing is at neither end.  What would see through it is a census that
> follows a conjunct's VALUE through the relays that carry it, and nobody has
> built one.

This is that instrument, for the SUPPLY direction: for every application in
`StreamAccum` of a constant with a `_ ∨ True` binder, resolve the argument in
that position to what actually decides it.

## What it follows, and what each answer means

* `PAY` / `DECLINE` — an `Or.inl` / `Or.inr` written at the call site.  These
  are the only two a term census can see, and they are **314 of 659** edges.
* `VIA g` — the argument is the result of calling `g`, so `g`'s own conclusion
  decides it.  This is the case items 199–211 called a relay and never counted;
  it is the largest resolvable share after the two above, and `Or.imp` — the
  combinator item 201 named — is **39** of it.
* `SPLIT g` — the argument is the result of a case split at the call site, so
  the site decides it on two branches rather than one.
* `RELAY` — the argument is one of the enclosing constant's OWN binders, so the
  decision belongs to ITS callers.  This is the only shape item 211 looked for.
* `FIELD of …` / `LOCAL …` — the argument was unpacked from a destructuring.
  `LOCAL` is this census's own blind spot, kept as a NUMBER rather than a
  sentence: every one of them is a park field or a bundle field, which is
  items 198 and 200's census and not this one's.

A `have`-bound hypothesis is followed through its beta-redex, and a case
split's alternatives are entered with their constructor fields marked and
their generalized binders bound to the matcher's own trailing arguments — so
`have h := f x` reads `VIA f` and not `LOCAL h`.  That single step is the whole
difference from reading the compiler's error text, which prints the BINDER NAME
at every one of them and cannot tell a premise from a `have`.

## The reading that made this item

Item 211 falsified `content_dispatch_routed`'s optional contexts one at a time
and read, off the compiler's own error text, that of its 8 call sites **seven
relay their own `h_keyctx`** — and concluded that `KeyPackPunt.noKeyContext`
"is not missing an input, it is behind a RELAY".  All seven errors do print
`h_keyctx`.  Neither `accum_content_pending` nor `accum_content_on_noPending`
HAS an `h_keyctx` binder: both write `have h_keyctx := keyctx_of_preprocess …`,
which this census reads as `VIA`.  **Six of the seven call a producer; one
relays.**  A name is not a provenance.

Checked against the compiler, by narrowing to a fixpoint (DOCS item 212):
narrowing the premise to `∨ False` breaks 8 sites; also narrowing
`keyctx_of_preprocess`'s conclusion REPAIRS six of them — which a site that
truly relayed a premise could not be, since it would not be calling that lemma
— and the remaining supply closes at **four** decisions, three of them inside
`keyctx_of_preprocess` and one `Or.inr trivial`.

## The `∨ True` binder of `content_dispatch_routed` nobody had counted

`optTargets` below reads the optional binders off the TYPE rather than off a
hand-written list.  `content_dispatch_routed` has **six**, not the five item
211's script enumerated: `h_ref` was never in it. -/

namespace L4YAML.Tests.Guards.RelaySupplyCensus

open Lean Elab Command

def isOptTy (e : Expr) : Bool :=
  e.isAppOfArity ``Or 2 && (e.getArg! 1).isConstOf ``True

/-- `(index, name)` of every `_ ∨ True` binder of a type, with the arity. -/
def optBinders (ty : Expr) : Array (Nat × Name) × Nat := Id.run do
  let mut out := #[]; let mut t := ty; let mut i := 0
  repeat match t with
    | .forallE n a b _ =>
        if isOptTy a then out := out.push (i, n)
        i := i + 1; t := b
    | _ => break
  return (out, i)

partial def lamDepth : Expr → Nat
  | .lam _ _ b _ => lamDepth b + 1
  | _ => 0

abbrev OptMap := Std.HashMap Name (Array (Nat × Name))

/-- A binder in scope: its name, whether its type is `_ ∨ True`, the VALUE it
    is bound to when it is a `have`/`let`/beta-redex binder, and where it came
    from when it is a case split's own. -/
structure Bnd where
  name : Name
  opt  : Bool
  val  : Option Expr
  src  : String := ""
deriving Inhabited

/-- What supplies an argument.  `d` is the number of binders in scope where the
    argument lives; `st` is the binder stack OUTERMOST first, so the enclosing
    constant's own `n` binders are `st[0] … st[n-1]` and `.bvar k` names
    `st[d-1-k]`.  A bound value is followed at the depth it was bound at, which
    is what keeps the de Bruijn indices inside it meaningful. -/
partial def resolve (isMech : Name → Bool) (st : Array Bnd) (n : Nat) :
    Nat → Expr → Nat → String × Option Nat
  | _, _, 0 => ("DEEP", none)
  | d, e, fuel+1 =>
    let f := e.getAppFn
    if f.isConstOf ``Or.inl then ("PAY", none)
    else if f.isConstOf ``Or.inr then ("DECLINE", none)
    else match f with
      | .const c _ =>
          if isMech c then (s!"SPLIT {c}", none) else (s!"VIA {c}", none)
      | .bvar k =>
          if d - 1 - k < st.size ∧ k < d then
            let j := d - 1 - k
            if j < n then ("RELAY", some j)
            else match st[j]!.val with
              | some v => resolve isMech st n j v fuel
              | none =>
                  if st[j]!.src != "" then (st[j]!.src, none)
                  else (s!"LOCAL {st[j]!.name}{if st[j]!.opt then ":opt" else ":?"}",
                        none)
          else ("OOB", none)
      | .lam .. => ("BETA", none)
      | _ => ("OTHER", none)

/-- Caller `C` supplies callee `g`'s optional premise `idx` with `how`. -/
structure Edge where
  caller : Name
  callee : Name
  idx    : Nat
  how    : String
  tgt    : Option Nat := none
deriving Inhabited

def appEdges (isMech : Name → Bool) (self : Name) (n : Nat) (st : Array Bnd)
    (g : Name) (obs : Array (Nat × Name)) (args : Array Expr) : Array Edge :=
  Id.run do
    let mut out : Array Edge := #[]
    for (i, _) in obs do
      if h : i < args.size then
        let (how, tgt) := resolve isMech st n st.size args[i] 24
        out := out.push ⟨self, g, i, how, tgt⟩
      else out := out.push ⟨self, g, i, "UNDERAPPLIED", none⟩
    return out

/-- The case-split MECHANISM, as opposed to a supply site. -/
def isMechanism (env : Environment) (g : Name) : Bool :=
  (Lean.Meta.isMatcherCore env g) ||
  (match g with
   | .str _ s => s == "casesOn" || s == "recOn" || s == "brecOn" || s == "rec"
                 || s == "below" || s == "ndrec" || s == "ndrecOn"
                 || s.startsWith "match_"
   | _ => false)

/-- Where a split's alternatives sit in its argument list, and how many binders
    of each are constructor FIELDS.  Covers `match` auxiliaries and the
    `casesOn` recursors `obtain`/`rcases` elaborate to. -/
structure Shape where
  numParams    : Nat
  numDiscrs    : Nat
  numAlts      : Nat
  altNumParams : Array Nat
deriving Inhabited

def splitShape (env : Environment) (g : Name) : Option Shape :=
  match Lean.Meta.getMatcherInfoCore? env g with
  | some i => some ⟨i.numParams, i.numDiscrs, i.numAlts, i.altNumParams⟩
  | none =>
    match g with
    | .str t "casesOn" =>
      match env.find? t with
      | some (.inductInfo iv) =>
          let fields := iv.ctors.map fun c =>
            match env.find? c with
            | some (.ctorInfo cv) => cv.numFields
            | _ => 0
          some ⟨iv.numParams, iv.numIndices + 1, iv.ctors.length, fields.toArray⟩
      | _ => none
    | _ => none

mutual

/-- One alternative of a case split: its first `k` binders are constructor
    FIELDS of `disc`; the rest take the split's trailing arguments. -/
partial def walkAlt (env : Environment) (m : OptMap) (self : Name) (n : Nat)
    (st : Array Bnd) (k : Nat) (disc : String) (trailing : Array Expr) :
    Expr → Array Edge → Array Edge
  | e, acc => Id.run do
    let mut st := st
    let mut e := e
    let mut i := 0
    repeat
      match e with
      | .lam bn t b _ =>
          if i < k then
            st := st.push ⟨bn, isOptTy t, none, s!"FIELD of {disc}"⟩
          else
            let v := if h : i - k < trailing.size then some trailing[i - k] else none
            st := st.push ⟨bn, isOptTy t, v, if v.isSome then "" else s!"GEN of {disc}"⟩
          e := b; i := i + 1
      | _ => break
    return walk env m self n st e acc

partial def walk (env : Environment) (m : OptMap) (self : Name) (n : Nat) :
    Array Bnd → Expr → Array Edge → Array Edge
  | st, .lam bn t b _, acc => walk env m self n (st.push ⟨bn, isOptTy t, none, ""⟩) b acc
  | st, .forallE bn t b _, acc =>
      walk env m self n (st.push ⟨bn, isOptTy t, none, ""⟩) b acc
  | st, .letE bn t v b _, acc =>
      walk env m self n (st.push ⟨bn, isOptTy t, some v, ""⟩) b (walk env m self n st v acc)
  | st, .mdata _ e, acc => walk env m self n st e acc
  | st, .proj _ _ e, acc => walk env m self n st e acc
  | st, e@(.app _ _), acc =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .lam .. =>
          -- a beta-redex: `have x := v; body` and friends.  Binding the
          -- binders to their arguments is what makes a `have`-built hypothesis
          -- read as its producer instead of as a nameless local.
          let rec peel (st : Array Bnd) (body : Expr) (i : Nat) (acc : Array Edge) :
              Array Edge :=
            match body, (if i < args.size then some args[i]! else none) with
            | .lam bn t b _, some a =>
                peel (st.push ⟨bn, isOptTy t, some a, ""⟩) b (i+1)
                  (walk env m self n st a acc)
            | body, _ =>
                walk env m self n st body
                  ((args.extract i args.size).foldl
                    (fun a x => walk env m self n st x a) acc)
          peel st f 0 acc
      | .const g _ =>
          if isMechanism env g then
            match splitShape env g with
            | some info => Id.run do
                let firstAlt := info.numParams + 1 + info.numDiscrs
                let lastAlt := firstAlt + info.numAlts
                let disc := if h : info.numParams + 1 < args.size then
                    (resolve (isMechanism env) st n st.size args[info.numParams + 1] 24).1
                  else "?"
                let trailing := if lastAlt < args.size then
                    args.extract lastAlt args.size else #[]
                let mut acc := acc
                for idx in [0:args.size] do
                  let a := args[idx]!
                  if firstAlt ≤ idx && idx < lastAlt then
                    acc := walkAlt env m self n st info.altNumParams[idx - firstAlt]!
                      disc trailing a acc
                  else acc := walk env m self n st a acc
                return acc
            | none => args.foldl (fun a x => walk env m self n st x a) acc
          else
            let acc := args.foldl (fun a x => walk env m self n st x a) acc
            match m[g]? with
            | none => acc
            | some obs => acc ++ appEdges (isMechanism env) self n st g obs args
      | _ => args.foldl (fun a x => walk env m self n st x a) acc
  | _, _, acc => acc

end

def optMap : CommandElabM OptMap := do
  let env ← getEnv
  let mut mm : OptMap := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    let (obs, _) := optBinders ci.type
    if obs.isEmpty then continue
    mm := mm.insert nm obs
  return mm

def ns : Name := `L4YAML.Proofs.StreamAccum

/-- Every optional-premise supply edge inside the module declaring `anchor`,
    with the count of constants whose value has fewer leading lambdas than
    their type has binders — the census refuses to read those, and says so. -/
def edges (anchor : Name) : CommandElabM (Array Edge × Nat) := do
  let env ← getEnv
  let m ← optMap
  let modIdx := env.getModuleIdxFor? anchor
  let mut acc : Array Edge := #[]
  let mut skipped := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if isMechanism env nm then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let (_, n) := optBinders ci.type
    if lamDepth v < n then skipped := skipped + 1; continue
    acc := walk env m nm n #[] v acc
  return (acc, skipped)

end L4YAML.Tests.Guards.RelaySupplyCensus

namespace L4YAML.Tests.Guards.RelaySupplyCensus

open Lean Elab Command

/-- The supply census, pinned.  `DECLINE` and `PAY` are the two a term census
    can see; every other row is a supply it cannot.  **345 of 659 edges — 52 %
    — are decided somewhere other than the site that writes them**, which is
    the share items 199, 201 and 211 each described in a sentence and none
    could count.  `LOCAL` is this census's OWN blind spot, kept as a number:
    each is a field unpacked from a park or a bundle, which is items 198 and
    200's census.  `skipped` counts constants whose value has fewer leading
    lambdas than their type has binders — the census will not read those, and
    a rewrite that hides a proof from it has to move this number. -/
def expectedTally : String :=
  "edges=659 skipped=31 [DECLINE=271, FIELD=5, LOCAL=56, PAY=43, RELAY=56, \
SPLIT=149, VIA=79]"

/-- **The row item 211 read off the compiler's error text and got wrong.**  All
    eight of these print `h_keyctx` when the premise is narrowed; six of them
    are `have h_keyctx := keyctx_of_preprocess …` and one is the binder.  If a
    `have` is ever turned back into a premise — or a premise into a `have` —
    this list moves and the DOCS sentence resting on it has to move with it. -/
def expectedSeed : List String :=
  ["accum_content_on_noPending VIA keyctx_of_preprocess",
   "accum_content_on_noPending VIA keyctx_of_preprocess",
   "accum_content_pending DECLINE",
   "accum_content_pending VIA keyctx_of_preprocess",
   "accum_content_pending VIA keyctx_of_preprocess",
   "accum_content_pending VIA keyctx_of_preprocess",
   "accum_content_pending VIA keyctx_of_preprocess",
   "content_dispatch_after_close RELAY"]

/-- Every lemma that DECIDES an optional premise for someone else, and how
    often.  Thirteen constants carry the module's whole producer surface, and
    `Or.imp` — the combinator item 201 named as the blind spot and nobody
    counted — is 39 of the 79.  `keyctx_of_preprocess`'s **7** is the seed's
    six plus `content_dispatch_after_close`'s own premise, and the compiler
    agrees with both halves: narrowing its conclusion repairs exactly seven
    sites (DOCS item 212). -/
def expectedProducers : List String :=
  ["2 VIA FlowBaseRoutes.key",
   "2 VIA FlowBaseRoutes.vslot",
   "2 VIA flowKeyRoute_of_root",
   "2 VIA flowVPack_of_close",
   "2 VIA markerctx_of_landing",
   "2 VIA nodocctx_of_preprocess",
   "2 VIA suffixctx_of_landing",
   "3 VIA flowKeyRoute_of_open",
   "39 VIA Or.imp",
   "4 VIA dite",
   "4 VIA explFrameValueLine",
   "7 VIA keyctx_of_preprocess",
   "8 VIA frameChainUnion"]

/-- **Read off the TYPE, not off a list.**  Item 211's falsification script
    enumerated five optional contexts of `content_dispatch_routed` by hand;
    the lemma states SIX.  A hand-typed knob chooses its own answer, so the
    census names them itself. -/
def expectedOptBinders : List String :=
  ["18 h_keyctx", "20 h_suffixctx", "21 h_nodocctx", "22 h_markerctx",
   "24 h_ref", "25 h_propsctx"]

end L4YAML.Tests.Guards.RelaySupplyCensus

open Lean Elab Command L4YAML.Tests.Guards.RelaySupplyCensus in
run_cmd do
  let (es, skipped) ← edges (ns ++ `content_dispatch_routed)
  let mut tally : Std.HashMap String Nat := {}
  for e in es do
    let k := (e.how.splitOn " ").head!
    tally := tally.insert k ((tally.getD k 0) + 1)
  let gotTally := s!"edges={es.size} skipped={skipped} {
    (tally.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotTally != expectedTally then
    throwError "the relay supply census moved.\nexpected: {expectedTally}\ngot:      {gotTally}"
  let seed := (es.filter (fun e =>
    e.callee == ns ++ `content_dispatch_routed && e.idx == 18)).map (fun e =>
      s!"{e.caller.getString!} {e.how.replace "L4YAML.Proofs.StreamAccum." ""}")
  if seed.qsort.toList != expectedSeed then
    throwError "the SEED's supply moved.\nexpected ({expectedSeed.length}):\n{
      String.intercalate "\n" expectedSeed}\ngot ({seed.size}):\n{
      String.intercalate "\n" seed.qsort.toList}"
  let mut vt : Std.HashMap String Nat := {}
  for e in es.filter (·.how.startsWith "VIA") do
    vt := vt.insert e.how ((vt.getD e.how 0) + 1)
  let prods := ((vt.toList.map (fun (k,v) =>
    s!"{v} {k.replace "L4YAML.Proofs.StreamAccum." ""}")).mergeSort (· ≤ ·))
  if prods != expectedProducers then
    throwError "the PRODUCER surface moved.\nexpected ({expectedProducers.length}):\n{
      String.intercalate "\n" expectedProducers}\ngot ({prods.length}):\n{
      String.intercalate "\n" prods}"
  let env ← getEnv
  let some ci := env.find? (ns ++ `content_dispatch_routed) | throwError "no seed lemma"
  let obs := ((optBinders ci.type).1.map (fun (i, n) => s!"{i} {n}")).toList
  if obs != expectedOptBinders then
    throwError "the seed's OPTIONAL BINDERS moved.\nexpected ({
      expectedOptBinders.length}):\n{String.intercalate "\n" expectedOptBinders}\ngot ({
      obs.length}):\n{String.intercalate "\n" obs}"
