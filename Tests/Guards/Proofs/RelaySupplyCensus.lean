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

* `PAY` / `DECLINE` — an `Or.inl` / `Or.inr` written at the call site, on every
  branch there is.  These are the only two a term census can see, and they are
  ~~**314 of 659**~~ **315 of 659** edges — item 216's descent found one more,
  a chain of six splitters that agree.  **Item 218: a `PAY` is an answer about
  the PROOF, and it does not promise the site survives a narrowing.**  The one
  chain of six is a `have` whose ascribed type is the wide `_ ∨ True` and whose
  proof pays it on every branch; narrowing the field it fills breaks the USE
  site while the census is right that nothing declines there.  It is named in
  `expectedCollapsedEdge` because N-218 broke at exactly it.
* `VIA g` — the argument is the result of calling `g`, so `g`'s own conclusion
  decides it.  This is the case items 199–211 called a relay and never counted.
  ~~It is the largest resolvable share after the two above, and `Or.imp` — the
  combinator item 201 named — is **39** of it.~~  **Item 213: `Or.imp` and
  `dite` are PIPES and decide nothing**, and **item 214 followed all 43 of
  them** — `resolve` now has the pipe list (`pipeArg`), so this row is **36**
  edges over 11 constants and every one of them names a lemma.  It is the
  SMALLEST of the four hidden shares, not the largest.
* `SPLIT g` — the argument is the result of a case split at the call site, so
  the site decides it on two branches rather than one.  ~~At **156** this is the
  largest hidden share~~ — **it was never a hidden share at all, and this bullet
  said so before anything measured it.**  `resolve` enters every arm now (item
  216), and of the **328** leaves under the **155** that survive, **168 are
  `DECLINE` and 160 are `PAY` and NONE is anything else**: a split is the site
  writing both answers, once per branch.  What the row hides is not a decider —
  it is the BRANCH, and `expectedSplitLanding` is where that is counted.  156
  splits, 66 distinct splitters, 151 of them two-armed and not one of them a
  single-constructor destructuring.  **Item 217 took the branch**: **145 of the
  155 branch on a value the CALLER supplied**, and **99 of those on a premise
  that is itself a `_ ∨ True`** — the site writes both answers because its own
  caller may have declined.  Only TEN branch on a fact the site derives, and
  `expectedSiteDecided` names every one of them.  **Item 218 asked whether the
  declining branch can be SELECTED** and joined this row against the supply
  rows for the first time: of the 36 `(lemma, premise)` pairs behind the 99,
  **not one has a DECLINE arm nothing can select** — `dead=0` — and only **8**
  have a caller that declines them where they are branched on.  See
  `expectedDeclineReach`.
* `RELAY` — the argument is one of the enclosing constant's OWN binders, so the
  decision belongs to ITS callers.  This is the only shape item 211 looked for.
  **68**, of which 12 arrived through a pipe — **and this row is not what a
  relay costs.**  Item 217 measured a further **99** edges that read `SPLIT`
  and branch on one of these same optional binders: the site cases on whether
  its caller declined and answers in kind, which is a relay with a case
  analysis around it.  See `expectedSplitBranch`.
* `FIELD of g#i on d` — the argument is field `i` of the constructor that split
  `d`, so items 198 and 200's census decides it and not this one.  **58**, and
  53 of them are a field of the pending park the caller was handed: the row
  reads `FIELD of PendingNode.casesOn#23 on RELAY` and `pendingProps`' own
  telescope names index 23 `h_closeFE`, which is the premise being supplied.
  Field-to-same-field, on every one of the 53.  **Item 218 followed the field
  to its CONSTRUCTOR** (`altCtorField`; all **58** resolve) and that is where
  the answer turned out to live: `expectedDeclineReach`'s **`parkHop`** counts
  the branch premises whose supply is a park field and nothing else, and it is
  the majority of them — which is why `RELAY` and `FIELD` are followed and
  everything else is a terminal.
* `LOCAL …` — a binder this census will not name.  **27**, and unlike item 212's
  82 this is not a blind spot with a sentence attached: 20 are lambdas in one
  lemma's alternative bodies and 7 sit under a SATURATED pipe, which transports
  a function nobody applies.  Both are honest locals.  The 55 that used to swell
  this row were under an OVER-APPLIED pipe — see `peelPipe`.

A `have`-bound hypothesis is followed through its beta-redex, a `let` is bound
and followed, and a case split's alternatives are entered with their constructor
fields marked and their generalized binders bound to the matcher's own trailing
arguments — so `have h := f x` reads `VIA f` and not `LOCAL h`.  That single step is the whole
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
    is bound to when it is a `have`/`let`/beta-redex binder, where it came from
    when it is a case split's own, and `dep` — the DEPTH ITS VALUE LIVES AT.

    `dep` is what makes a multi-binder beta-redex readable.  Every argument of
    `(fun x y z => b) a₁ a₂ a₃` lives at the depth the redex was found at, but
    the binders sit at that depth, +1 and +2, so following `a₂` at `y`'s stack
    INDEX reads its de Bruijn variables one binder off.  The two agree for the
    first binder and only for the first, which is why this went unseen: every
    beta-redex item 212 met was a one-binder `have`.  Item 215's `peelPipe`
    peels up to thirteen at a time — see `expectedTally`. -/
structure Bnd where
  name   : Name
  opt    : Bool
  val    : Option Expr
  src    : String := ""
  dep    : Nat := 0
  /-- When this binder is a constructor FIELD, the enclosing constant's binder
      index the split's discriminant ROOTS at — so a field of a relayed datum
      still names the premise it was carved out of.  Item 217: 46 of the 145
      relay-rooted splits reach their premise only through this. -/
  srcTgt : Option Nat := none
  /-- When this binder is a constructor FIELD, the CONSTRUCTOR it is a field of
      and the binder index of that field in the constructor's own type.
      `srcTgt` names the premise the datum ARRIVED at, and for a park field
      that premise is a `PendingNode` rather than a `_ ∨ True`, so the supply
      chase dead-ends there; this names the field itself, where the park's
      CONSTRUCTION sites can be asked what they put in it.  Item 218:
      `expectedDeclineReach`'s `parkHop` counts the branch premises that reach
      their decline only through this. -/
  srcFld : Option (Name × Nat) := none
deriving Inhabited

/-- Which argument of a PIPE carries the decision.  Item 213 named these in the
    DOWNWARD direction and this census had no list: before item 214 a pipe was
    reported as `VIA <the combinator>`, which names what carried the answer and
    not what decided it.  `Or.imp` alone was **39 of the 79 `VIA` edges**.

    `dite`/`ite` are deliberately NOT here.  Downward they are pipes, because a
    route census collects EVERY route and takes both arms; upward this census
    has to name ONE decider, and a two-armed decision written at the call site
    is what it already calls `SPLIT` — see `isTwoArm`. -/
def pipeArg : Name → Option Nat
  | ``Or.imp => some 6
  | ``Or.imp_left | ``Or.imp_right => some 4
  | ``Eq.mpr | ``Eq.mp | ``cast => some 3
  | ``Eq.ndrec | ``Eq.rec => some 3
  | ``id => some 1
  | _ => none

/-- A pipe with two arms: the site decides, on two branches.  Both arms of all
    four occurrences in `StreamAccum` disagree, so reporting the common answer
    when the arms agree would be a knob with nothing behind it.  Item 216
    descended them and the four still disagree — two instruments, one sentence,
    and this is the cross-check. -/
def isTwoArm : Name → Bool
  | ``dite | ``ite => true
  | _ => false

/-- `(major, firstAlt, numAlts, binders-per-alt)` for a two-arm pipe, so
    `resolve` can enter its arms the way it enters a matcher's.

    `ite` is deliberately absent.  `dite`'s arms each bind the decision's proof
    and `ite`'s bind nothing, so the two need different shapes — and `ite`
    occurs **zero** times in this module (measured, item 216: the 156 splits are
    66 distinct splitters and `ite` is not one of them).  A shape nothing
    instantiates is not evidence, so `ite` keeps reading `SPLIT ite`, which is
    what it read before. -/
def twoArmShape : Name → Option (Nat × Nat × Nat × Array Nat)
  | ``dite => some (1, 3, 2, #[1, 1])
  | _ => none

/-- The loose de Bruijn indices of an expression, relative to where it sits.
    Item 217 uses them for one question only: does an `Or.inl`/`Or.inr`'s
    argument refer to ANYTHING in scope, or is it self-contained? -/
partial def looseRefs : Expr → Nat → Array Nat → Array Nat
  | .bvar k, off, acc => if k ≥ off then acc.push (k - off) else acc
  | .app f a, off, acc => looseRefs a off (looseRefs f off acc)
  | .lam _ t b _, off, acc => looseRefs b (off+1) (looseRefs t off acc)
  | .forallE _ t b _, off, acc => looseRefs b (off+1) (looseRefs t off acc)
  | .letE _ t v b _, off, acc =>
      looseRefs b (off+1) (looseRefs v off (looseRefs t off acc))
  | .mdata _ e, off, acc => looseRefs e off acc
  | .proj _ _ e, off, acc => looseRefs e off acc
  | _, _, acc => acc

/-- `closed` when the `Or` constructor's argument mentions nothing in scope —
    `Or.inr trivial` is the whole of it — and `free` when it hands back
    something it was given.  **This is what makes a premise narrowing
    predictable by line**: a `closed` DECLINE cannot break when the premise its
    split branches on is narrowed, because it never touches it.  Item 217
    measured 164 of the 168 `DECLINE` leaves `closed` and used the count to
    forecast N-217's error set before the edit; see `expectedSplitBranch`. -/
def orArgRefs (args : Array Expr) : String :=
  if h : 2 < args.size then
    (if (looseRefs args[2] 0 #[]).isEmpty then "closed" else "free")
  else "?"

/-- What `resolve` found: the answer, the enclosing constant's binder index when
    the answer is `RELAY`, the pipes crossed on the way, the SPLITS crossed, and
    the LEAVES of the decision tree when the answer is still a split.  `pipes`
    and `splits` are what make the two landings re-derivable instead of
    asserted, and `leaves` is what makes `SPLIT` interrogable at all: before
    item 216 the row named the splitter and stopped. -/
structure Res where
  how     : String
  tgt     : Option Nat := none
  pipes   : List String := []
  splits  : List String := []
  leaves  : Array String := #[]
  /-- The DISCRIMINANT chain of a surviving split, with relay indices: WHICH
      BRANCH is taken is decided by this, and by nothing the site writes.
      Item 217. -/
  disc    : String := ""
  /-- The enclosing constant's binder index the discriminant chain roots at,
      when it roots at one at all — 145 of the 155 do. -/
  rootTgt : Option Nat := none
  /-- One entry per entry of `leaves`: `orArgRefs` at that leaf. -/
  leafSrc : Array String := #[]
  /-- Item 218: the constructor field a `FIELD` answer was carved from. -/
  fldTgt  : Option (Name × Nat) := none
deriving Inhabited

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

/-- The CONSTRUCTOR an alternative of a `casesOn` belongs to, and the binder
    index in that constructor's own type which alternative-binder `i` names.

    A matcher returns `none` and says so: its alternatives are patterns, not
    constructors, and inventing a constructor for one would be a knob.  Measured
    (item 218): all **58** `FIELD` edges in this module resolve, so the census
    does not currently need the matcher case — which is a fact about this
    module and not a property of the instrument. -/
def altCtorField (env : Environment) (g : Name) (alt : Nat) (i : Nat) :
    Option (Name × Nat) :=
  match g with
  | .str t "casesOn" =>
    match env.find? t with
    | some (.inductInfo iv) =>
        match iv.ctors[alt]? with
        | some c => some (c, iv.numParams + i)
        | none => none
    | _ => none
  | _ => none

/-- What supplies an argument.  `d` is the number of binders in scope where the
    argument lives; `st` is the binder stack OUTERMOST first, so the enclosing
    constant's own `n` binders are `st[0] … st[n-1]` and `.bvar k` names
    `st[d-1-k]`.  **That indexing is only meaningful while `st.size == d`**, so
    every place this function pushes a binder truncates `st` to `d` first:
    following a value at its own `dep` leaves the stack longer than the depth,
    and item 216 measured the skew reachable (8 occurrences) and moving zero
    edges.  A bound value is followed at the depth it was bound at, which is
    what keeps the de Bruijn indices inside it meaningful.  A PIPE is followed
    into the argument that carries the decision, and a lambda is entered rather
    than reported — three `Or.imp` edges and all eight `dite` arms stop at a
    `BETA` otherwise.

    A SPLIT is entered on every arm, and the answers are joined: agreeing arms
    give one answer and the splitter joins `splits`, disagreeing arms keep the
    `SPLIT` label and their answers become `leaves`.  There is no third rule,
    because a split that answers differently on different branches HAS no single
    answer — see `expectedSplitLanding`. -/
partial def resolve (env : Environment) (isMech : Name → Bool) (st : Array Bnd)
    (n : Nat) : Nat → Expr → Nat → Res
  | _, _, 0 => { how := "DEEP" }
  | d, e, fuel+1 =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConstOf ``Or.inl then { how := "PAY", leafSrc := #[orArgRefs args] }
    else if f.isConstOf ``Or.inr then
      { how := "DECLINE", leafSrc := #[orArgRefs args] }
    else match f with
      | .const c _ =>
          match pipeArg c with
          | some i =>
              if h : i < args.size then
                let r := resolve env isMech st n d args[i] fuel
                { r with pipes := c.toString :: r.pipes }
              else { how := s!"PIPE-UNDERAPPLIED {c}", pipes := [c.toString] }
          | none =>
            if isTwoArm c || isMech c then
              let pipes0 := if isTwoArm c then [c.toString] else []
              let shp := if isTwoArm c then twoArmShape c else
                match splitShape env c with
                | some i => some (i.numParams + i.numDiscrs,
                                  i.numParams + 1 + i.numDiscrs, i.numAlts, i.altNumParams)
                | none => none
              match shp with
              | none => { how := s!"SPLIT {c}", pipes := pipes0 }
              | some (major, firstAlt, numAlts, altNP) =>
                if firstAlt + numAlts > args.size then { how := s!"SPLIT {c}", pipes := pipes0 }
                else Id.run do
                  -- enter every arm: a split's answer is one answer PER BRANCH,
                  -- so the only thing that can be reported as ONE answer is a
                  -- split whose arms all agree — and exactly one of the 156
                  -- does.  The rest keep the `SPLIT` label and carry their
                  -- leaves, which is what `expectedSplitLanding` reads.
                  let dres := if h : major < args.size then
                      resolve env isMech st n d args[major] fuel else { how := "?" }
                  -- the arm LABEL stays `dres.how`, so every `src` string this
                  -- census has ever printed is byte-identical; the INDEXED
                  -- chain rides beside it in `disc`, and `rootTgt` is where it
                  -- bottoms out.  Item 217.
                  let disc := dres.how
                  let dchain :=
                    if dres.how == "RELAY" then s!"RELAY#{dres.tgt.getD 0}"
                    else if dres.disc != "" then s!"{dres.how} on {dres.disc}"
                    else dres.how
                  let rootTgt := if dres.how == "RELAY" then dres.tgt else dres.rootTgt
                  let mut arms : Array Res := #[]
                  for idx in [firstAlt:firstAlt+numAlts] do
                    let need := altNP[idx - firstAlt]!
                    let mut stA := st.extract 0 d
                    let mut dA := d
                    let mut body := args[idx]!
                    for j in [0:need] do
                      match body with
                      | .lam bn t b _ =>
                          let lbl := if isTwoArm c then s!"GUARD of {c}#{j}"
                                     else s!"FIELD of {c}#{j} on {disc}"
                          stA := stA.push
                            { name := bn, opt := isOptTy t, val := none, src := lbl,
                              srcTgt := rootTgt,
                              srcFld := altCtorField env c (idx - firstAlt) j }
                          body := b; dA := dA + 1
                      | _ => pure ()
                    arms := arms.push (resolve env isMech stA n dA body fuel)
                  let keys := (arms.map (fun r => s!"{r.how}|{r.tgt}")).qsort.toList.eraseDups
                  if keys.length == 1 then
                    let r0 := arms[0]!
                    return { r0 with splits := c.toString :: r0.splits }
                  else
                    let lv := arms.foldl
                      (fun a r => a ++ (if r.leaves.isEmpty then #[r.how] else r.leaves)) #[]
                    let ls := arms.foldl (fun a r => a ++
                      (if r.leaves.isEmpty then
                         (if r.leafSrc.isEmpty then #[""] else r.leafSrc)
                       else r.leafSrc)) #[]
                    return { how := s!"SPLIT {c}", pipes := pipes0, leaves := lv,
                             disc := dchain, rootTgt := rootTgt, leafSrc := ls }
            else { how := s!"VIA {c}" }
      | .bvar k =>
          if d - 1 - k < st.size ∧ k < d then
            let j := d - 1 - k
            if j < n then { how := "RELAY", tgt := some j, rootTgt := some j }
            else match st[j]!.val with
              | some v => resolve env isMech st n st[j]!.dep v fuel
              | none =>
                  if st[j]!.src != "" then
                    { how := st[j]!.src, rootTgt := st[j]!.srcTgt, fldTgt := st[j]!.srcFld }
                  else { how := s!"LOCAL {st[j]!.name}{if st[j]!.opt then ":opt" else ":?"}" }
          else { how := "OOB" }
      | .letE bn t v b _ =>
          -- three arms of the 155 splits are a `let`, and item 212's `resolve`
          -- had no case for them: they read `OTHER`, which is the census
          -- declining to answer.  Bind and continue, exactly as `walk` does.
          resolve env isMech ((st.extract 0 d).push { name := bn, opt := isOptTy t, val := some v, dep := d })
            n (d+1) b fuel
      | .lam .. =>
          -- a beta-redex, or a bare function reached through a pipe: bind what
          -- arguments there are and resolve the body at the new depth.  The
          -- arguments all live at `d0`, not at the depth each binder sits at.
          -- `st` is truncated to `d` first: `st[d-1-k]` is only the binder a
          -- `.bvar k` names while INDEX == DEPTH, and following a value at its
          -- own `dep` leaves `st` longer than `d`.  Item 216 measured this
          -- reachable (8 occurrences) and moving ZERO edges.
          let d0 := d
          let rec peel (st : Array Bnd) (body : Expr) (i : Nat) (d : Nat) : Res :=
            match body with
            | .lam bn t b _ =>
                let v := if h : i < args.size then some args[i] else none
                peel (st.push { name := bn, opt := isOptTy t, val := v, dep := d0 }) b (i+1) (d+1)
            | body => resolve env isMech st n d body fuel
          peel (st.extract 0 d) f 0 d
      | _ => { how := "OTHER" }

/-- Caller `C` supplies callee `g`'s optional premise `idx` with `how`. -/
structure Edge where
  caller : Name
  callee : Name
  idx    : Nat
  how    : String
  tgt    : Option Nat := none
  pipes  : List String := []
  splits : List String := []
  leaves : Array String := #[]
  disc    : String := ""
  rootTgt : Option Nat := none
  leafSrc : Array String := #[]
  /-- Item 218: the constructor field a `FIELD` supply was carved from. -/
  fldTgt  : Option (Name × Nat) := none
deriving Inhabited

def appEdges (env : Environment) (isMech : Name → Bool) (self : Name) (n : Nat)
    (st : Array Bnd) (g : Name) (obs : Array (Nat × Name)) (args : Array Expr) :
    Array Edge :=
  Id.run do
    let mut out : Array Edge := #[]
    for (i, _) in obs do
      if h : i < args.size then
        let r := resolve env isMech st n st.size args[i] 24
        out := out.push { caller := self, callee := g, idx := i, how := r.how,
                          tgt := r.tgt, pipes := r.pipes, splits := r.splits,
                          leaves := r.leaves, disc := r.disc, rootTgt := r.rootTgt,
                          leafSrc := r.leafSrc, fldTgt := r.fldTgt }
      else out := out.push { caller := self, callee := g, idx := i, how := "UNDERAPPLIED" }
    return out

/-- The case-split MECHANISM, as opposed to a supply site. -/
def isMechanism (env : Environment) (g : Name) : Bool :=
  (Lean.Meta.isMatcherCore env g) ||
  (match g with
   | .str _ s => s == "casesOn" || s == "recOn" || s == "brecOn" || s == "rec"
                 || s == "below" || s == "ndrec" || s == "ndrecOn"
                 || s.startsWith "match_"
   | _ => false)

/-- A constant's arity, counted off its TYPE's leading binders.  An application
    carrying MORE arguments than this is OVER-APPLIED: what it returns is being
    used as a function, and for a PIPE that means the pipe is transporting a
    function to a beta-redex — see `peelPipe`. -/
def arityOf (env : Environment) (g : Name) : Nat :=
  match env.find? g with
  | some ci => (optBinders ci.type).2
  | none => 0

mutual

/-- An over-applied PIPE is a beta-redex with a pipe in the middle: the pipe
    transports a FUNCTION and the trailing arguments are what it is applied to.
    Peel the transported lambda against them, binding each binder to its value
    exactly as the plain beta-redex case does, and recording the depth those
    values live at.

    This is the shape 55 of item 214's 82 `LOCAL` edges were in, and it is NOT
    the shape item 214 forecast.  Item 214 predicted a pipe standing between a
    split and its alternative, to be descended and then shaped; the census
    reports ZERO such sites.  What is actually there is a `cases` whose whole
    motive was transported: `Eq.ndrec` with arity 6 carrying 10 to 19
    arguments, the extra ones being the park's own fields. -/
partial def peelPipe (env : Environment) (m : OptMap) (self : Name) (n : Nat)
    (trailing : Array Expr) (d0 : Nat) : Array Bnd → Expr → Nat →
    Array Edge → Array Edge
  | st, body, j, acc =>
    match body with
    | .lam bn t b _ =>
        if h : j < trailing.size then
          peelPipe env m self n trailing d0
            (st.push { name := bn, opt := isOptTy t, val := some trailing[j], dep := d0 }) b (j+1)
            (walk env m self n st trailing[j] acc)
        else walk env m self n st body acc
    | body =>
        walk env m self n st body
          ((trailing.extract j trailing.size).foldl
            (fun a x => walk env m self n st x a) acc)

/-- One alternative of a case split: its first `k` binders are constructor
    FIELDS of `disc`; the rest take the split's trailing arguments. -/
partial def walkAlt (env : Environment) (m : OptMap) (self : Name) (n : Nat)
    (st : Array Bnd) (k : Nat) (disc : String) (dtgt : Option Nat) (splitter : Name)
    (alt : Nat) (trailing : Array Expr) : Expr → Array Edge → Array Edge
  | e, acc => Id.run do
    let d0 := st.size
    let mut st := st
    let mut e := e
    let mut i := 0
    repeat
      match e with
      | .lam bn t b _ =>
          if i < k then
            st := st.push { name := bn, opt := isOptTy t, val := none,
                            src := s!"FIELD of {splitter}#{i} on {disc}", srcTgt := dtgt,
                            srcFld := altCtorField env splitter alt i }
          else
            let v := if h : i - k < trailing.size then some trailing[i - k] else none
            let gsrc : String := if v.isSome then "" else s!"GEN of {disc}"
            st := st.push { name := bn, opt := isOptTy t, val := v, src := gsrc, dep := d0 }
          e := b; i := i + 1
      | _ => break
    return walk env m self n st e acc

partial def walk (env : Environment) (m : OptMap) (self : Name) (n : Nat) :
    Array Bnd → Expr → Array Edge → Array Edge
  | st, .lam bn t b _, acc => walk env m self n (st.push { name := bn, opt := isOptTy t, val := none }) b acc
  | st, .forallE bn t b _, acc =>
      walk env m self n (st.push { name := bn, opt := isOptTy t, val := none }) b acc
  | st, .letE bn t v b _, acc =>
      walk env m self n (st.push { name := bn, opt := isOptTy t, val := some v, dep := st.size }) b
        (walk env m self n st v acc)
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
          let d0 := st.size
          let rec peel (st : Array Bnd) (body : Expr) (i : Nat) (acc : Array Edge) :
              Array Edge :=
            match body, (if i < args.size then some args[i]! else none) with
            | .lam bn t b _, some a =>
                peel (st.push { name := bn, opt := isOptTy t, val := some a, dep := d0 }) b (i+1)
                  (walk env m self n st a acc)
            | body, _ =>
                walk env m self n st body
                  ((args.extract i args.size).foldl
                    (fun a x => walk env m self n st x a) acc)
          peel st f 0 acc
      | .const g _ =>
          if h : (pipeArg g).isSome && arityOf env g < args.size
                 && (pipeArg g).get! < args.size then Id.run do
            -- the pipe treatment `resolve` has had since item 214, one level
            -- up: an over-applied pipe is a beta-redex and its trailing
            -- arguments are what the transported function receives.
            let i := (pipeArg g).get!
            let ar := arityOf env g
            let mut acc := acc
            for idx in [0:ar] do
              if idx != i then acc := walk env m self n st args[idx]! acc
            return peelPipe env m self n (args.extract ar args.size) st.size st
              args[i]! 0 acc
          else if isMechanism env g then
            match splitShape env g with
            | some info => Id.run do
                let firstAlt := info.numParams + 1 + info.numDiscrs
                let lastAlt := firstAlt + info.numAlts
                -- the major premise sits AFTER the indices: `params, motive,
                -- indices…, major`.  Reading `numParams + 1` reads the first
                -- INDEX of an indexed inductive — `PendingNode` has four, so
                -- every field of the park was labelled `of VIA Bool.false`.
                let major := info.numParams + info.numDiscrs
                let dres := if h : major < args.size then
                    resolve env (isMechanism env) st n st.size args[major] 24
                  else { how := "?" }
                let disc := dres.how
                let dtgt := if dres.how == "RELAY" then dres.tgt else dres.rootTgt
                let trailing := if lastAlt < args.size then
                    args.extract lastAlt args.size else #[]
                let mut acc := acc
                for idx in [0:args.size] do
                  let a := args[idx]!
                  if firstAlt ≤ idx && idx < lastAlt then
                    acc := walkAlt env m self n st info.altNumParams[idx - firstAlt]!
                      disc dtgt g (idx - firstAlt) trailing a acc
                  else acc := walk env m self n st a acc
                return acc
            | none => args.foldl (fun a x => walk env m self n st x a) acc
          else
            let acc := args.foldl (fun a x => walk env m self n st x a) acc
            match m[g]? with
            | none => acc
            | some obs => acc ++ appEdges env (isMechanism env) self n st g obs args
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

/-- The head constant of binder `i` of `c`'s TYPE — read off the declaration
    and never off a proof term.  This is the INDEPENDENT artifact the
    discriminant column is checked against: `expectedSplitBranch`'s
    `agree=99/99` compares the splitter's own declared major type with the type
    of the premise the chain roots at, and the two censuses share no code path
    to reach them. -/
def binderHead (env : Environment) (c : Name) (i : Nat) : Name :=
  match env.find? c with
  | none => `NOCONST
  | some ci => Id.run do
      let mut t := ci.type
      let mut k := 0
      repeat
        match t with
        | .forallE _ ty b _ =>
            if k == i then return (ty.getAppFn.constName?.getD `NOTCONST)
            t := b; k := k + 1
        | _ => break
      return `SHORT

/-- The NAME of binder `i` of `c`'s type, for naming a branch's host premise. -/
def binderName (env : Environment) (c : Name) (i : Nat) : Name :=
  match env.find? c with
  | none => `NOCONST
  | some ci => Id.run do
      let mut t := ci.type
      let mut k := 0
      repeat
        match t with
        | .forallE nm _ b _ =>
            if k == i then return nm
            t := b; k := k + 1
        | _ => break
      return `SHORT

/-- The splitter's own major-premise index, so its DECLARED discriminant type
    can be read off its type rather than inferred from the application. -/
def majorOf (env : Environment) (c : Name) : Option Nat :=
  if isTwoArm c then (twoArmShape c).map (fun s => s.1)
  else (splitShape env c).map (fun i => i.numParams + i.numDiscrs)

/-- Whether binder `j` of `c` is itself one of the `_ ∨ True` premises. -/
def isOptBinder (env : Environment) (c : Name) (j : Nat) : Bool :=
  match env.find? c with
  | some ci => (optBinders ci.type).1.any (fun q => q.1 == j)
  | none => false

/-- Every supply edge, keyed by the premise it fills.  The join item 217 could
    not run: a split knows the premise `(caller, rootTgt)` its discriminant
    roots at, and a supply edge knows the premise `(callee, idx)` it fills, and
    both indices come from `optBinders`' single counter — so the two can be
    joined, and the join PARTITIONS the census (`accounted` below must equal
    `edges`, which is the control). -/
abbrev SupplyMap := Std.HashMap String (Array Edge)

def keyOf (c : Name) (i : Nat) : String := s!"{c}#{i}"

def supplyMap (es : Array Edge) : SupplyMap := Id.run do
  let mut m : SupplyMap := {}
  for e in es do
    let k := keyOf e.callee e.idx
    m := m.insert k ((m.getD k #[]).push e)
  return m

/-- Chase supply UPWARD to the labels it terminates in.  `RELAY` and `FIELD`
    decide nothing — the first hands the caller's own premise down, the second
    hands a park's field down — so both are followed; every other label is a
    terminal, and a `SPLIT`'s leaves come back tagged `br` so a decline written
    on one branch stays distinguishable from a flat one.

    **The `FIELD` hop is an OVER-APPROXIMATION and deliberately so.**  It
    collects every construction site of that constructor in the module, not only
    the ones that can reach this call site, so a `dead` verdict cannot be
    manufactured by a path the chase failed to find.  Where the constructor
    carries no optional field at all — `And.intro` and `Exists.intro` do not;
    those data were destructured out of a nested payload rather than out of a
    park — it falls back to `rootTgt`, the premise the whole nest arrived at.

    `seen` is per PATH: **8 of the 161 nodes' chases reach a cycle**, the
    documented one being the value-line carrier that funds the pack that funds
    the park again.  Without the guard this does not terminate. -/
partial def terminals (m : SupplyMap) (seen : Std.HashSet String) (k : String)
    (depth : Nat) : Std.HashSet String × Nat × Array String :=
  if seen.contains k then (({} : Std.HashSet String).insert "CYCLE", depth, #[])
  else
    let seen := seen.insert k
    match m[k]? with
    | none => (({} : Std.HashSet String).insert "ORPHAN", depth, #[])
    | some arr => Id.run do
        let mut out : Std.HashSet String := {}
        let mut d := depth
        let mut sites : Array String := #[]
        for e in arr do
          let hd := (e.how.splitOn " ").head!
          let up : Option String :=
            if hd == "RELAY" then e.tgt.map (keyOf e.caller)
            else if hd == "FIELD" then
              (match e.fldTgt.map (fun (c, i) => keyOf c i) with
               | some nk => if m.contains nk then some nk else e.rootTgt.map (keyOf e.caller)
               | none => e.rootTgt.map (keyOf e.caller))
            else none
          if hd == "RELAY" || hd == "FIELD" then
            match up with
            | some nk =>
                let (t, d2, si) := terminals m seen nk (depth + 1)
                for x in t.toList do out := out.insert x
                sites := sites ++ si
                d := max d d2
            | none => out := out.insert s!"{hd}-unresolved"
          else if hd == "SPLIT" then
            for lf in e.leaves do out := out.insert s!"br{(lf.splitOn " ").head!}"
            if e.leaves.any (fun lf => (lf.splitOn " ").head! == "DECLINE") then
              sites := sites.push e.caller.toString
          else
            out := out.insert hd
            if hd == "DECLINE" then sites := sites.push e.caller.toString
        return (out, d, sites)

def setStr (t : Std.HashSet String) : String :=
  String.intercalate "+" (t.toList.mergeSort (· ≤ ·))

/-- The first hop of a branch premise's supply chase, named.  A `FIELD` names
    the park field it was carved from (`pendingBlock.h_closeF`), which is the
    form the module's own comments use and therefore checkable against them by
    a route this census does not take. -/
def hopName (env : Environment) (e : Edge) : String :=
  match e.fldTgt with
  | some (c, i) =>
      -- the last TWO components: `PendingNode.pendingBlock`, `And.intro`.  One
      -- component alone renders `And.intro` as `intro`, which names nothing.
      let base := match c with
        | .str (.str _ a) b => s!"{a}.{b}"
        | _ => c.toString
      s!"{base}.{binderName env c i}"
  | none => match e.tgt with
            | some t => s!"{(binderName env e.caller t)}@{e.caller.getString!}"
            | none => "-"

/-- The supply census, pinned.  `DECLINE` and `PAY` are the two a term census
    can see; every other row is a supply it cannot.  ~~**345 of 659 edges — 52 %
    — are decided somewhere other than the site that writes them**~~ — **that
    sentence was wrong from the day it was written, and the `SPLIT` bullet forty
    lines above it says why**: a split IS decided at the site, on branches, and
    it was 156 of the 345.  Corrected by item 216, which entered the arms and
    found every one of the 328 leaves to be a `PAY` or a `DECLINE`: **189 of 659
    edges — 29 % — are decided somewhere other than the site**, and 470 are
    decided at it, 315 unconditionally and 155 per branch.  189 is the share
    items 199, 201 and 211 each described in a sentence and none could count.

    The COMPOSITION has moved three times and the walk has not gained or lost an
    edge: following the pipes (item 214) took `VIA` 79 → 36 and put the
    difference into `LOCAL` (+26), `RELAY` (+10) and `SPLIT` (+7); following the
    OVER-APPLIED ones (item 215) took `LOCAL` 82 → 27, 53 of them to `FIELD` and
    2 to `RELAY`; entering the arms (item 216) took `SPLIT` 156 → 155 and `PAY`
    43 → 44.  `edges=659` is the invariant that matters: if IT ever moves, the
    walk gained or lost an EDGE, which is a different event and a worse one.
    A row moving from hidden to visible, as one did here, is not that.
    `skipped` counts constants whose value has fewer leading lambdas than their
    type has binders — the census will not read those, and a rewrite that hides
    a proof from it has to move this number. -/
def expectedTally : String :=
  "edges=659 skipped=31 [DECLINE=271, FIELD=58, LOCAL=27, PAY=44, RELAY=68, \
SPLIT=155, VIA=36]"

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
    often.  ~~Thirteen constants carry the module's whole producer surface~~,
    and `Or.imp` — the combinator item 201 named as the blind spot and nobody
    counted — is 39 of the 79.  `keyctx_of_preprocess`'s **7** is the seed's
    six plus `content_dispatch_after_close`'s own premise, and the compiler
    agrees with both halves: narrowing its conclusion repairs exactly seven
    sites (DOCS item 212).

    **Item 213: two of the thirteen are not producers.**  `Or.imp` (39) and
    `dite` (4) are PIPES — they carry a decision made elsewhere — so 43 of those
    79 edges named a combinator and not a decider.  **Item 214 followed them and
    they are gone from this list**: the surface is 36 edges over the 11 constants
    below, and every row names a lemma.  Where the 43 went is
    `expectedPipeLanding`, and the answer is that NONE of them is a producer. -/
def expectedProducers : List String :=
  ["2 VIA FlowBaseRoutes.key",
   "2 VIA FlowBaseRoutes.vslot",
   "2 VIA flowKeyRoute_of_root",
   "2 VIA flowVPack_of_close",
   "2 VIA markerctx_of_landing",
   "2 VIA nodocctx_of_preprocess",
   "2 VIA suffixctx_of_landing",
   "3 VIA flowKeyRoute_of_open",
   "4 VIA explFrameValueLine",
   "7 VIA keyctx_of_preprocess",
   "8 VIA frameChainUnion"]

/-- **Where the 43 pipes land (DOCS item 214).**  Item 213 measured that 43 of
    this census's 79 `VIA` edges named a combinator rather than a decider and
    could say nothing about what stood behind them; `resolve` now follows them,
    and this is the answer.  `producers=0` is the row that matters and it is
    asserted as a COUNT, not by being absent from the list: **not one of the 43
    reaches a producer.**  `piped=43` is the same total item 213 derived by
    parsing the row above, now measured rather than parsed, so the two
    instruments can still disagree.

    The landing, read as provenance: 26 are a park or bundle FIELD, 10 are the
    caller's own binder, 7 are a case split — 3 an `Or.casesOn` reached through
    the pipe and 4 the `dite` arms themselves.

    **Item 215 split the first row where item 214 could only assert it.**  Item
    214 read the 26 off the probe by hand and reported 21 of them bound inside
    an `Eq.ndrec`; `peelPipe` now resolves exactly those 21 to `FIELD`, and the
    5 that stay `LOCAL` are the ones under a SATURATED pipe, which transports a
    function nobody applies.  The hand count and the instrument agree, and the
    total is still 43 with still no producer among them. -/
def expectedPipeLanding : String :=
  "piped=43 producers=0 [Or.imp⇒FIELD=21, Or.imp⇒LOCAL=5, Or.imp⇒RELAY=10, \
Or.imp⇒SPLIT=3, dite⇒SPLIT=4]"

/-- What the SPLITs decide (DOCS item 216), and the row that matters is
    `elsewhere=0`: **not one leaf of any case split in this module is decided
    anywhere but at the site.**  It is asserted as a COUNT, not by being absent
    from the list.

    `resolve` enters every arm now.  An arm's answer is an answer per BRANCH, so
    the only split that can be reported as one answer is one whose arms agree —
    and exactly ONE of the 156 does, a chain of six splitters
    (`Or.casesOn→Exists.casesOn→Exists.casesOn→And.casesOn→And.casesOn→dite`)
    that all land on `PAY`.  The other 155 keep the `SPLIT` label and carry
    their leaves, which is what the shape list below counts.

    **That one is named in `expectedCollapsedEdge` as of item 218**, and naming
    it was not bookkeeping: it is the site N-218 broke at where the join
    predicted no break, because its `have` ascribes the wide `_ ∨ True` while
    its proof pays on all six branches. -/
def expectedSplitLanding : String :=
  "survived=155 collapsed=1 leaves=328 elsewhere=0 [DECLINE=168, PAY=160] \
[DECLINE|DECLINE|DECLINE|PAY=1, DECLINE|DECLINE|DECLINE|PAY|PAY|PAY=1, \
DECLINE|DECLINE|PAY=8, DECLINE|DECLINE|PAY|PAY|PAY=1, DECLINE|PAY=143, \
DECLINE|PAY|PAY=1]"

/-- **Which BRANCH is taken (DOCS item 217).**  Item 216 resolved what a split
    WRITES — both answers, one per arm.  What it could not say was which arm the
    runtime takes, and the answer is that the site almost never chooses:
    **145 of the 155 surviving splits branch on a value the CALLER supplied**,
    99 of them directly on one of the caller's own binders and 46 through a
    constructor field carved out of one.  Ten — and only ten — branch on a fact
    the site derives for itself; they are listed in `expectedSiteDecided`.

    ~~99 split on a `RELAY`~~ — that was item 216's own discriminant column read
    only as far as its bare `RELAY` rows, and it skipped both the 46 chains that
    reach a relay through a field and the 9 nested splits that reach one through
    another split.  **The number is 145.**

    Of the 145, **99 root at a premise that is itself a `_ ∨ True`** — the site
    is casing on whether its OWN CALLER declined, and then declining in the arm
    where the caller did.  Their host premises are `expectedBranchPremises`.

    `agree=99/99` is the control, and it is a cross-check rather than a restated
    count: for every split whose discriminant is a bare relay, the splitter's
    DECLARED major-premise type — read off the splitter's own type by
    `majorOf`/`binderHead` — is compared with the type of the premise the chain
    roots at, read off the enclosing lemma's type.  Neither reading goes through
    the proof term the census walks, so a wrong `major` index would show up here
    as a disagreement rather than as a plausible column.

    The leaf rows are `orArgRefs`: **164 of the 168 `DECLINE` leaves are
    `closed`**, an `Or.inr trivial` that mentions nothing in scope, and all 160
    `PAY` leaves are `free`.  That asymmetry is what made N-217 predictable by
    line: a `closed` decline cannot break when the premise its split branches on
    is narrowed. -/
def expectedSplitBranch : String :=
  "splits=155 leaves=328 relayRooted=145 siteDecided=10 optionalRoot=99 \
plainRoot=46 agree=99/99 disagree=0 [DECLINE-closed=164, DECLINE-free=4, PAY-free=160]"

/-- **The ten splits the site decides for itself**, which is the whole residue
    of the branch question after `expectedSplitBranch`.  Four are a `dite` on a
    condition the site tests (`VIA Eq`, `VIA LE.le`); five case an `Or`-valued
    fact the site derives (`Nat.eq_zero_or_pos`, `frameChainUnion`); one reaches
    its fact through a nested split (`preprocess_some_savedKey_shape`).

    `dite`'s `major` is argument 1 — the PROPOSITION, not a proof of it — so
    `VIA Eq` and `VIA LE.le` naming a type here is the instrument reading the
    condition, not losing the discriminant. -/
def expectedSiteDecided : List String :=
  ["1 accum_block_on_closeThenBlock :: dite on VIA Eq ⇒ DECLINE|PAY",
   "1 accum_block_on_pendingBlock :: dite on VIA Eq ⇒ DECLINE|PAY",
   "1 accum_block_on_pendingBlock :: dite on VIA LE.le ⇒ DECLINE|DECLINE|PAY|PAY|PAY",
   "1 accum_block_on_pendingBlockContent :: dite on VIA Eq ⇒ DECLINE|PAY",
   "1 accum_content_pending :: Or.casesOn on VIA Nat.eq_zero_or_pos ⇒ \
DECLINE|DECLINE|DECLINE|PAY",
   "1 accum_flow_open_depth0 :: accum_flow_open_depth0.match_1_18 on SPLIT Or.casesOn \
on VIA preprocess_some_savedKey_shape ⇒ DECLINE|PAY",
   "2 accum_block_pending :: Or.casesOn on VIA Nat.eq_zero_or_pos ⇒ DECLINE|PAY",
   "2 question_open_map :: question_open_map.match_1_7 on VIA frameChainUnion ⇒ \
DECLINE|PAY"]

/-- **The premises the branch is taken on**, by binder NAME, for the 99 splits
    whose discriminant roots at an optional premise of the enclosing lemma.
    These are the pending park's own optional contexts — the same names items
    198/200 counted as park fields — which is why narrowing one of them is a
    question about the park's callers and not about the lemma that splits on it.

    **Item 218 ran that question and the answer is in `expectedBranchSupply`**,
    one row per `(lemma, premise)` pair naming the park field each reads from
    and the labels its own supply terminates in. -/
def expectedBranchPremises : List String :=
  ["1 h_mapF", "1 h_mapFV", "1 h_mk", "1 h_pr", "1 h_routeS", "1 h_sfx", "1 h_valFV",
   "10 h_closeFV_old", "12 h_closeF_old", "3 h_cov", "3 h_kslotUp_old", "3 h_seqF_old",
   "4 h_closeFV108", "4 h_expl", "4 h_kslotUp", "4 h_resV_land", "4 h_routeF",
   "4 h_routeFV", "5 h_seqF168", "7 h_closeF99", "8 h_kslot_old", "8 h_vslot",
   "9 h_kslot"]

/-- **Is a DECLINE arm ever SELECTED (DOCS item 218).**  Item 217 named, for
    each of the 99 optional-rooted splits, the premise its branch is taken on.
    It could not say whether any caller ever takes the declining branch.  This
    joins the two halves of the census that had never met — every split's
    `(caller, rootTgt)` against every supply edge's `(callee, idx)` — and
    chases the result upward to the labels it terminates in.

    `dead=0` is the row that matters: **not one of the 36 branch premises has a
    DECLINE arm that nothing can select.**  `direct=8` is the row that was a
    surprise: only 8 of the 36 have a caller that writes `Or.inr trivial`
    straight into them, so **a decline is almost never written where it is
    branched on** — 25 of the remaining 28 reach it through a park's
    construction sites, one hop up.

    `orphan=3` is the census DECLINING to answer and is reported apart from
    `dead` for that reason: those three leave the module at
    `colon_fires_implicit_key`/`colon_fires_props_key`'s `h_key`, and a walk
    that is scoped to one module cannot see who fills a premise from outside
    it.  This is the first item at which that horizon bit.

    `accounted` is the control: the join must PARTITION the census, so it has to
    equal `edges`.  `resolved` is the second: every `FIELD` edge must name a
    constructor field, or the `FIELD` hop is guessing. -/
def expectedDeclineReach : String :=
  "pairs=36 orphan=3 direct=8 closureDecline=33 dead=0 maxDepth=2 liveSplits=96 \
deadSplits=0 accounted=659/659 nodes=161 fieldEdges=58 fieldResolved=58 withCycle=8 \
declineWriters=19 parkHop=21"

/-- **Every branch premise, with what its own callers supply and where that
    bottoms out.**  `⇐` names the FIRST hop — for a park field, the field
    itself (`pendingBlock.h_closeF`), which is the form the module's own
    comments use, so the row is checkable against them by a route this census
    does not take.  `⇒` is the terminal set, `br` marking a label reached on one
    branch of a split rather than flatly. -/
def expectedBranchSupply : List String :=
  ["h_closeF99 :: accum_content_on_pendingMapValue_indented#18 :: splits=7 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_closeF ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_closeFV108 :: accum_content_on_pendingMapValue_indented#20 :: splits=4 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_closeFV ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_closeFV_old :: accum_block_on_pendingBlock#30 :: splits=4 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_closeFV ⇒ DECLINE+brDECLINE+brPAY",
   "h_closeFV_old :: accum_block_on_pendingBlockContent#36 :: splits=2 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_closeFV ⇒ brDECLINE+brPAY",
   "h_closeFV_old :: accum_content_on_pendingBlock_indented#29 :: splits=4 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_closeFV ⇒ DECLINE+brDECLINE+brPAY",
   "h_closeF_old :: accum_block_on_pendingBlockContent#35 :: splits=1 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_closeF ⇒ brDECLINE+brPAY",
   "h_closeF_old :: accum_content_on_pendingBlock_indented#14 :: splits=11 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_closeF ⇒ DECLINE+PAY",
   "h_cov :: indicator_open_map#27 :: splits=3 sup=4 [DECLINE=1,SPLIT=3] ⇐ - ⇒ DECLINE+brDECLINE+brPAY",
   "h_expl :: accum_content_on_pendingMapValue_indented#15 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_expl ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_expl :: explFrameValueLine#3 :: splits=1 sup=4 [RELAY=4] ⇐ h_expl@accum_content_on_pendingMapValue_indented ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_kslot :: accum_block_on_pendingBlock#15 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslot ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslot :: accum_block_on_pendingBlockContent#16 :: splits=1 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_kslot ⇒ brDECLINE+brPAY",
   "h_kslot :: accum_content_on_pendingMapValue_indented#17 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_kslot ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslot :: colon_open_map_implicit#11 :: splits=1 sup=1 [FIELD=1] ⇐ And.intro.left ⇒ ORPHAN",
   "h_kslot :: colon_open_map_props#11 :: splits=1 sup=1 [FIELD=1] ⇐ And.intro.left ⇒ ORPHAN",
   "h_kslotUp :: accum_block_on_pendingBlock#29 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslotUp ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslotUp :: accum_block_on_pendingBlockContent#34 :: splits=1 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_kslotUp ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslotUp_old :: accum_content_on_pendingBlock_indented#28 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslotUp ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslot_old :: accum_content_on_pendingBlock_indented#13 :: splits=8 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslot ⇒ DECLINE+brDECLINE+brPAY",
   "h_mapF :: accum_block_on_closeThenBlock#29 :: splits=1 sup=11 [DECLINE=7,FIELD=2,RELAY=2] ⇐ h_mapF109@accum_block_on_pendingContent,-,PendingNode.pendingMapValue.h_frames ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_mapFV :: accum_block_on_closeThenBlock#31 :: splits=1 sup=11 [DECLINE=7,FIELD=2,RELAY=2] ⇐ h_mapFV108@accum_block_on_pendingContent,-,PendingNode.pendingMapValue.h_framesV ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_mk :: accum_block_on_closeThenBlock#21 :: splits=1 sup=11 [DECLINE=10,PAY=1] ⇐ - ⇒ DECLINE+PAY",
   "h_pr :: accum_block_on_closeThenBlock#30 :: splits=1 sup=11 [DECLINE=9,SPLIT=2] ⇐ - ⇒ DECLINE+brDECLINE+brPAY",
   "h_resV_land :: colon_open_map#26 :: splits=3 sup=1 [RELAY=1] ⇐ h_resV_land@indicator_open_map ⇒ DECLINE+brDECLINE+brPAY",
   "h_resV_land :: question_open_map#27 :: splits=1 sup=1 [RELAY=1] ⇐ h_resV_land@indicator_open_map ⇒ DECLINE+brDECLINE+brPAY",
   "h_routeF :: colon_open_map_implicit#12 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeF :: colon_open_map_props#12 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeFV :: colon_open_map_implicit#13 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeFV :: colon_open_map_props#13 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeS :: colon_open_map_implicit#27 :: splits=1 sup=1 [FIELD=1] ⇐ And.intro.right ⇒ ORPHAN",
   "h_seqF168 :: accum_content_on_pendingMapValue_indented#35 :: splits=5 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_seqF ⇒ DECLINE+brDECLINE+brPAY",
   "h_seqF_old :: accum_content_on_pendingBlock_indented#15 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_seqF ⇒ DECLINE+PAY",
   "h_sfx :: accum_block_on_closeThenBlock#20 :: splits=1 sup=11 [DECLINE=10,PAY=1] ⇐ - ⇒ DECLINE+PAY",
   "h_valFV :: accum_block_on_closeThenBlock#32 :: splits=1 sup=11 [DECLINE=9,FIELD=2] ⇐ -,PendingNode.pendingMapValue.h_closeFV ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_vslot :: accum_block_on_closeThenBlock#12 :: splits=5 sup=11 [DECLINE=10,SPLIT=1] ⇐ - ⇒ DECLINE+brDECLINE+brPAY",
   "h_vslot :: accum_content_on_pendingMapValue_indented#16 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_vslot ⇒ DECLINE+PAY+brDECLINE+brPAY"]

/-- **The lemmas that actually WRITE the declines** the 99 splits branch on,
    and how often each is reached.  The COUNT is per chase and per edge — a
    lemma that declines a field which several branch premises read is counted
    once for each of them — so the **19 names** are the claim and the numbers
    are how the machine re-derives them.

    This is the domain a corpus census would have to cover, and it is the
    number item 218 exists to produce: **the runtime question is not 99 splits
    wide, it is these nineteen lemmas' construction sites wide.**  Most of them
    write their declines while CONSTRUCTING a park rather than at the site that
    branches — `expectedBranchSupply`'s `⇐` column names the park field for
    every row that does, and `direct=8` is the same fact counted the other way
    round. -/
def expectedDeclineWriters : List String :=
  ["10 accum_block_on_pendingContent",
   "11 accum_block_on_noPending",
   "12 accum_content_on_pendingBlock_indented",
   "12 accum_content_on_pendingMapValue_indented",
   "13 colon_open_map",
   "15 colon_open_map_explicit",
   "16 colon_open_map_implicit",
   "16 colon_open_map_props",
   "16 compact_open_map",
   "18 accum_block_on_closeThenBlock",
   "18 accum_block_on_pendingBlockContent",
   "2 colon_fires_implicit_key",
   "2 colon_fires_props_key",
   "2 question_open_map",
   "32 accum_content_pending",
   "33 accum_block_on_pendingBlock",
   "41 accum_block_pending",
   "8 accum_step_flow",
   "8 content_dispatch_routed"]

/-- **The ONE collapsed split, named.**  Item 216 measured `collapsed=1` and
    described its splitter chain; nothing named the edge.  It is named here
    because N-218 broke at exactly it: narrowing `pendingBlock.h_closeF` gave
    the five lemmas the join predicted, and this site — whose proof pays on
    every one of its six branches — was the eighth error where seven were
    forecast.  **A `PAY` is an answer about the PROOF and a narrowing is a
    question about the TYPE**: the `have` at
    [StreamAccum.lean:21853](../../../L4YAML/Proofs/Production/StreamAccum.lean)
    ascribes the wide `_ ∨ True` and pays it on every branch, so the census is
    right that nothing declines there and the narrowing breaks at the USE site
    all the same. -/
def expectedCollapsedEdge : String :=
  "accum_block_on_closeThenBlock → PendingNode.pendingBlock#11 (h_closeF) = PAY via \
Or.casesOn→Exists.casesOn→Exists.casesOn→And.casesOn→And.casesOn→dite"

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
  -- where the pipes land, and that none of them lands on a producer
  let piped := es.filter (fun e => !e.pipes.isEmpty)
  let mut lt : Std.HashMap String Nat := {}
  for e in piped do
    lt := lt.insert s!"{String.intercalate "→" e.pipes}⇒{(e.how.splitOn " ").head!}"
      ((lt.getD s!"{String.intercalate "→" e.pipes}⇒{(e.how.splitOn " ").head!}" 0) + 1)
  let gotLanding := s!"piped={piped.size} producers={
    (piped.filter (·.how.startsWith "VIA")).size} {
    (lt.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotLanding != expectedPipeLanding then
    throwError "the PIPE LANDING moved.\nexpected: {expectedPipeLanding}\ngot:      {gotLanding}"
  -- what the SPLITs decide, and that not one of them decides it elsewhere
  let split := es.filter (·.how.startsWith "SPLIT")
  let coll := es.filter (fun e => !e.splits.isEmpty)
  let leaves := split.foldl (fun a e => a ++ e.leaves) #[]
  let mut lf : Std.HashMap String Nat := {}
  for a in leaves do
    let k := (a.splitOn " ").head!
    lf := lf.insert k ((lf.getD k 0) + 1)
  let mut sh : Std.HashMap String Nat := {}
  for e in split do
    let k := String.intercalate "|" (e.leaves.map (fun a => (a.splitOn " ").head!)).qsort.toList
    sh := sh.insert k ((sh.getD k 0) + 1)
  let gotSplit := s!"survived={split.size} collapsed={coll.size} leaves={leaves.size} \
elsewhere={(leaves.filter (fun a => a != "PAY" && a != "DECLINE")).size} {
    (lf.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)} {
    (sh.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotSplit != expectedSplitLanding then
    throwError "the SPLIT landing moved.\nexpected: {expectedSplitLanding}\ngot:      {gotSplit}"
  -- WHICH BRANCH (DOCS item 217): every surviving split's discriminant, chased
  -- to its root, with the splitter's own declared major type as the control.
  let env ← getEnv
  let pfx := "L4YAML.Proofs.StreamAccum."
  let relayRooted := split.filter (fun e => e.rootTgt.isSome)
  let optRooted := relayRooted.filter (fun e => isOptBinder env e.caller (e.rootTgt.getD 0))
  let direct := split.filter (fun e => e.disc.startsWith "RELAY#")
  let mut agree := 0
  let mut disagree : Array String := #[]
  for e in direct do
    let splitter := (e.how.splitOn " ").getLast!.toName
    match majorOf env splitter with
    | none => disagree := disagree.push s!"NOSHAPE {splitter}"
    | some m =>
        if binderHead env splitter m == binderHead env e.caller (e.rootTgt.getD 0) then
          agree := agree + 1
        else
          disagree := disagree.push s!"{e.caller.getString!}#{e.rootTgt.getD 0} {splitter}"
  let mut lsT : Std.HashMap String Nat := {}
  for e in split do
    for i in [0:e.leaves.size] do
      let k := s!"{e.leaves[i]!}-{if i < e.leafSrc.size then e.leafSrc[i]! else "?"}"
      lsT := lsT.insert k ((lsT.getD k 0) + 1)
  let gotBranch := s!"splits={split.size} leaves={
    split.foldl (fun a e => a + e.leaves.size) 0} relayRooted={relayRooted.size} \
siteDecided={split.size - relayRooted.size} optionalRoot={optRooted.size} \
plainRoot={relayRooted.size - optRooted.size} agree={agree}/{direct.size} \
disagree={disagree.size} {(lsT.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotBranch != expectedSplitBranch then
    throwError "the SPLIT BRANCH census moved.\nexpected: {
      expectedSplitBranch}\ngot:      {gotBranch}\ndisagreements: {disagree.toList}"
  let mut sd : Std.HashMap String Nat := {}
  for e in split.filter (fun e => e.rootTgt.isNone) do
    let shp := String.intercalate "|" (e.leaves.map (fun a => (a.splitOn " ").head!)).qsort.toList
    let k := s!"{e.caller.getString!} :: {
      ((e.how.splitOn " ").getLast!).replace pfx ""} on {
      e.disc.replace pfx ""} ⇒ {shp}"
    sd := sd.insert k ((sd.getD k 0) + 1)
  let gotSite := (sd.toList.map (fun (a,b) => s!"{b} {a}")).mergeSort (· ≤ ·)
  if gotSite != expectedSiteDecided then
    throwError "the SITE-DECIDED splits moved.\nexpected ({
      expectedSiteDecided.length}):\n{String.intercalate "\n" expectedSiteDecided}\ngot ({
      gotSite.length}):\n{String.intercalate "\n" gotSite}"
  let mut hp : Std.HashMap String Nat := {}
  for e in optRooted do
    let k := (binderName env e.caller (e.rootTgt.getD 0)).toString
    hp := hp.insert k ((hp.getD k 0) + 1)
  let gotHosts := (hp.toList.map (fun (a,b) => s!"{b} {a}")).mergeSort (· ≤ ·)
  if gotHosts != expectedBranchPremises then
    throwError "the BRANCH PREMISES moved.\nexpected ({
      expectedBranchPremises.length}):\n{String.intercalate "\n" expectedBranchPremises}\ngot ({
      gotHosts.length}):\n{String.intercalate "\n" gotHosts}"
  -- IS A DECLINE EVER SELECTED (DOCS item 218): the join of the two halves,
  -- chased upward to where the decline is actually written.
  let sm := supplyMap es
  let accounted := sm.toList.foldl (fun a (_, v) => a + v.size) 0
  let fld := es.filter (fun e => (e.how.splitOn " ").head! == "FIELD")
  let mut pairs : Std.HashMap String Nat := {}
  for e in optRooted do
    let k := keyOf e.caller (e.rootTgt.getD 0)
    pairs := pairs.insert k ((pairs.getD k 0) + 1)
  let mut supRows : Array String := #[]
  let mut nDirect := 0; let mut nDecl := 0; let mut nDead := 0; let mut nOrph := 0
  let mut maxD := 0; let mut liveS := 0; let mut deadS := 0; let mut nPark := 0
  let mut writers : Std.HashMap String Nat := {}
  for (k, nsplits) in pairs.toList do
    let parts := k.splitOn "#"
    let lem := (String.intercalate "#" (parts.dropLast)).toName
    let j := parts.getLast!.toNat!
    let sup := sm.getD k #[]
    let mut dt : Std.HashMap String Nat := {}
    for e in sup do
      let hd := (e.how.splitOn " ").head!
      dt := dt.insert hd ((dt.getD hd 0) + 1)
    let (ts, d, sites) := terminals sm {} k 0
    for w in sites do writers := writers.insert w ((writers.getD w 0) + 1)
    if dt.contains "DECLINE" then nDirect := nDirect + 1
    if ts.contains "DECLINE" || ts.contains "brDECLINE" then
      nDecl := nDecl + 1; liveS := liveS + nsplits
    else if ts.contains "ORPHAN" then nOrph := nOrph + 1
    else nDead := nDead + 1; deadS := deadS + nsplits
    maxD := max maxD d
    if sup.any (fun e => match e.fldTgt with
         | some (c, _) => (c.toString.splitOn ".").any (· == "PendingNode")
         | none => false) then nPark := nPark + 1
    let hops := String.intercalate "," ((sup.toList.map (hopName env)).eraseDups)
    supRows := supRows.push s!"{binderName env lem j} :: {
      lem.toString.replace pfx ""}#{j} :: splits={nsplits} sup={sup.size} [{
      String.intercalate "," ((dt.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·))
      }] ⇐ {hops} ⇒ {setStr ts}"
  let mut cyc := 0
  for (k, _) in sm.toList do
    let (ts, _, _) := terminals sm {} k 0
    if ts.contains "CYCLE" then cyc := cyc + 1
  let gotReach := s!"pairs={pairs.size} orphan={nOrph} direct={nDirect} \
closureDecline={nDecl} dead={nDead} maxDepth={maxD} liveSplits={liveS} \
deadSplits={deadS} accounted={accounted}/{es.size} nodes={sm.size} \
fieldEdges={fld.size} fieldResolved={(fld.filter (·.fldTgt.isSome)).size} \
withCycle={cyc} declineWriters={writers.size} parkHop={nPark}"
  if gotReach != expectedDeclineReach then
    throwError "the DECLINE REACH census moved.\nexpected: {
      expectedDeclineReach}\ngot:      {gotReach}"
  let gotSupply := supRows.qsort.toList
  if gotSupply != expectedBranchSupply then
    throwError "the BRANCH SUPPLY moved.\nexpected ({expectedBranchSupply.length}):\n{
      String.intercalate "\n" expectedBranchSupply}\ngot ({gotSupply.length}):\n{
      String.intercalate "\n" gotSupply}"
  let gotWriters := (writers.toList.map (fun (a,b) =>
    s!"{b} {a.replace pfx ""}")).mergeSort (· ≤ ·)
  if gotWriters != expectedDeclineWriters then
    throwError "the DECLINE WRITERS moved.\nexpected ({
      expectedDeclineWriters.length}):\n{String.intercalate "\n" expectedDeclineWriters}\ngot ({
      gotWriters.length}):\n{String.intercalate "\n" gotWriters}"
  let gotColl := String.intercalate "; " ((es.filter (fun e => !e.splits.isEmpty)).toList.map
    (fun e => s!"{e.caller.toString.replace pfx ""} → {
      e.callee.toString.replace pfx ""}#{e.idx} ({binderName env e.callee e.idx}) = {
      e.how} via {String.intercalate "→" e.splits}"))
  if gotColl != expectedCollapsedEdge then
    throwError "the COLLAPSED edge moved.\nexpected: {
      expectedCollapsedEdge}\ngot:      {gotColl}"
  let some ci := env.find? (ns ++ `content_dispatch_routed) | throwError "no seed lemma"
  let obs := ((optBinders ci.type).1.map (fun (i, n) => s!"{i} {n}")).toList
  if obs != expectedOptBinders then
    throwError "the seed's OPTIONAL BINDERS moved.\nexpected ({
      expectedOptBinders.length}):\n{String.intercalate "\n" expectedOptBinders}\ngot ({
      obs.length}):\n{String.intercalate "\n" obs}"
