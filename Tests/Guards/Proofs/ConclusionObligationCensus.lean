import Tests.Guards.Proofs.NarrowingWorthCensus

/-! # The obligation census (DOCS item 228)

Item 227 counted **27** declarations whose CONCLUSION `Or.inr trivial` proves,
and stopped there deliberately: "pick one of the 27 and narrow its CONCLUSION
— the operation that turns a theorem `Or.inr trivial` would prove into an
obligation, which is the only way to find out what the obligation costs."

This file is that operation and its price.

**Five of `FlowKeyLift`'s ten are narrowed** (`plain_toKey`,
`doubleQuoted_toKey`, `singleQuoted_toKey`, `sep_toKey`, and the
`sep_toBlockKey` relay): their `∨ True` is now `∨ <residue>`, read off the arm
each proof actually takes.  §5's re-run of item 227's own instrument reads
**22**, in both directions, which is the machine's receipt for the operation.

**What it cost.**  `scripts/narrow_conclusion.py` narrows a conclusion to
`∨ False` — the tightest narrowing there is, so the error count bounds what
ANY narrowing must pay — and lets `lake build` answer.  Over the 25 of the 27
that are lemmas at all, the answer is **182 sites**: 97 in `FlowKeyLift`, 84 in
`StreamAccum`, 1 in `PreprocessIndentStable`.  Three readings no earlier item
could make:

* **The price is mostly RELAY DAMAGE, not residue.**  `frameChainUnion` writes
  `Or.inr trivial` NOWHERE — its term census reads `res=0` — and narrowing its
  conclusion costs **11**, of which **10 are in other declarations**, spread
  from line 6618 to line 30527 of one module.  `flowKeyHead` is the same shape:
  1 own, 4 downstream.  **Narrowing a conclusion does not stop at the lemma.**
* **The obligation is concentrated.**  83 of `FlowKeyLift`'s 97 are in ONE
  lemma, `flowNode_toKey`.
* **A cheap probe under-prices it forty-fold.**  Narrowing only
  `flowNode_toKey`'s conclusion costs **2**: its proof is a single application
  of the flow grammar's 18-motive recursor, so the elaborator reports one
  mismatch for the whole term and the 83 sites stay hidden behind the eight
  `∨ True` MOTIVES.  An error count is a fact about how a proof is WRITTEN
  before it is a fact about the obligation.

**What it bought, and what it did not.**  §2.  The narrowing is worth exactly
the consumer's ability to REFUTE the residue, and `True` can never be refuted
(`true_residue_is_irrefutable`).  Three of the four new residues consume a line
break by construction; `SepResidue` does not, and §2 exhibits a span that
satisfies the residue AND the left disjunct at once.  **A narrowed residue that
overlaps its own left disjunct is not yet an obligation.**  Whether the other
three are tight is UNSETTLED here, for the same reason the family cannot be
narrowed at all: saying "this derivation consumed a break INSIDE this span"
needs a suffix lemma over the flow grammar, and §4 measures that the library
has **none**.
-/

set_option autoImplicit false

namespace Tests.Guards.ConclusionObligationCensus

open L4YAML L4YAML.Surface L4YAML.Proofs.FlowKeyLift
open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus
open Tests.Guards.NarrowingWorthCensus

/-! ## §1 The ladder's third rung

Item 226's first rung: a PREMISE `A ∨ True` is unconditionally inhabited, so it
buys nothing.  Item 227's second: narrowing it to `A` buys nothing either where
`A` is itself unconditionally inhabited.  Both are about premises.

Read on the CONCLUSION side the same two facts say something sharper.  A
conclusion `A ∨ True` is not a weak theorem about `A`; it is not a theorem
about `A` at all, because the proof that discharges it need not look at the
hypotheses.  And what a narrowing buys is exactly one thing — a consumer that
can REFUTE the residue gets the left disjunct — which is why `True` buys
nothing: no consumer can ever supply `¬ True`. -/

/-- A conclusion `A ∨ True` is proved without reading the hypotheses. -/
lemma noop_conclusion_ignores_hypotheses {P A : Prop} : P → (A ∨ True) :=
  fun _ => Or.inr trivial

/-- …so the statement IS the trivial one, whatever `A` is. -/
lemma noop_conclusion_is_trivial {A : Prop} : (A ∨ True) ↔ True :=
  ⟨fun _ => trivial, fun _ => Or.inr trivial⟩

/-- **What a narrowing buys**: a consumer that refutes the residue gets the
    left disjunct.  This is the whole content of the operation. -/
lemma narrowed_conclusion_pays {A R : Prop} (h : A ∨ R) (hr : ¬ R) : A :=
  h.resolve_right hr

/-- **…and why `True` buys nothing**: `¬ True` is uninhabited, so the right arm
    of `A ∨ True` is unreachable from every consumer, for ever. -/
lemma true_residue_is_irrefutable : ¬ (¬ (True : Prop)) :=
  fun h => h trivial

/-- The two together, as an iff: for a left disjunct that is not already free,
    `A ∨ R` yields `A` exactly when `R` is refutable. -/
lemma conclusion_eliminable_iff {A R : Prop} (hA : ¬ A) :
    ((A ∨ R) → A) ↔ ¬ R :=
  ⟨fun k hr => hA (k (Or.inr hr)), fun hr k => k.resolve_right hr⟩

/-! ## §2 The narrowing, performed — and one residue that is not an obligation

`sep_toKey` declines on `[70] s-separate-lines(n)`'s comment-delimited arm, and
`SepResidue` is that arm.  The arm is NOT "the separation crossed a line":
`[79] s-l-comments` has a comment-free `startOfLine` arm and `[63] s-indent(0)`
consumes nothing, so at a zero-width span at column 0 the residue holds — and
so does `[80] s-separate-in-line`, by its own `startOfLine` arm.  **Both
disjuncts are true at the same span**, which is exactly what a narrowing is
supposed to stop being true.

The module docstring of `FlowKeyLift` said the `True` side was "taken exactly
on a multi-line interior"; for the separation that is imprecise, and it is
corrected there, at item 228.

The other three residues (`PlainResidue`, `DoubleResidue`, `SingleResidue`)
each carry a `[28] b-break` or a `[29] b-non-content` in their own components,
so the same overlap is not available — but proving that they are DISJOINT from
their left disjunct needs "this derivation consumed a break inside this span",
and §4 measures that the instrument for that sentence does not exist.  They are
UNSETTLED, which is not a negative result. -/

/-- **The residue at a zero-width start-of-line span.** -/
lemma sepResidue_of_startOfLine (chars : List Char) :
    SepResidue 0 ⟨chars, 0⟩ ⟨chars, 0⟩ :=
  ⟨⟨chars, 0⟩, SSLComments.startOfLine chars _ (GStar.nil _),
    SFlowLinePrefix.mk 0 _ _ _ (SIndent.zero _) (GOpt.none _)⟩

/-- **…and the left disjunct at the same span**: `sep_toKey`'s narrowing does
    not partition its own input. -/
lemma sep_narrowing_does_not_partition (chars : List Char) :
    SSeparate 0 .blockKey ⟨chars, 0⟩ ⟨chars, 0⟩ ∧
      SepResidue 0 ⟨chars, 0⟩ ⟨chars, 0⟩ :=
  ⟨SSeparateInLine.startOfLine _, sepResidue_of_startOfLine chars⟩

/-- The narrowed lemma still has its left disjunct available there, so the
    overlap is not a gap in `sep_toKey` — it is a statement that the residue
    is weaker than the name suggests. -/
lemma sep_toKey_at_startOfLine (chars : List Char) :
    SSeparate 0 .blockKey ⟨chars, 0⟩ ⟨chars, 0⟩ :=
  (sep_narrowing_does_not_partition chars).1

/-! ## §2b Is the new residue itself vacuous?

Item 227's whole finding was that a narrowing buys nothing where the narrowed
face is unconditionally inhabited, so the first question to ask of a residue is
the one item 227 asked of a face.  Both of that item's witnesses are tried
here — `trivial`, and the empty-list prover
`⟨[], fun _ h => absurd h List.not_mem_nil⟩` that settled 22 of its 163 — and
neither settles any of the four, nor is any of them an `_ ∨ True` in disguise.

This is a NEGATIVE result about two specific provers and not a proof that the
residues are uninhabited; `sepResidue_of_startOfLine` shows one of them is
inhabited at a whole family of spans. -/

def expectedResidueProbe : String := "residues=4 byTrivial=0 byChain=0 optShaped=0"

open Meta in
run_cmd do
  let env ← getEnv
  let triv ← `(term| trivial)
  let chain ← `(term| ⟨[], fun _ h => absurd h List.not_mem_nil⟩)
  let mut n := 0
  let mut bt := 0
  let mut bc := 0
  let mut opt := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML.Proofs.FlowKeyLift).isPrefixOf nm then continue
    if !(nm.getString!.endsWith "Residue") then continue
    n := n + 1
    let (t, c, o) ← liftTermElabM do
      forallTelescope ci.type fun xs cod => do
        if !cod.isSort then return (false, false, false)
        let app := mkAppN (mkConst nm (ci.levelParams.map mkLevelParam)) xs
        return (← provableBy triv app, ← provableBy chain app, isOptTy (← whnf app))
    if t then bt := bt + 1
    if c then bc := bc + 1
    if o then opt := opt + 1
  let got := s!"residues={n} byTrivial={bt} byChain={bc} optShaped={opt}"
  if got != expectedResidueProbe then
    throwError "the residue probe moved.\nexpected: {expectedResidueProbe}\ngot:      {got}"

/-! ## §3 The obligation ledger

For every declaration item 227's instrument still selects, four numbers read
off the proof TERM and the environment: `res` — distinct subterms
`@Or.inr A True _ True.intro`; `imp` — the `∨ True` subterms the term carries
in a motive or an intermediate type; `prem` — `_ ∨ True` BINDERS in the type,
which is item 227's own population; `proj` — the declaration is a projection
and not a lemma at all.

`res` is a DAG count and undercounts by sharing: `props_toKey` writes
`Or.inr trivial` in two branches over the same span, so the two terms are
structurally identical and this walk sees one where the compiler sees two.
That is why `scripts/narrow_conclusion.py` exists, and why its number is the
one DOCS quotes. -/

partial def scanTerm (e : Expr) (seen : Std.HashSet Expr) (r i : Nat) :
    Std.HashSet Expr × Nat × Nat :=
  if seen.contains e then (seen, r, i) else
  let seen := seen.insert e
  let r := if e.isAppOfArity ``Or.inr 3 && (e.getArg! 1).isConstOf ``True then r + 1 else r
  let i := if isOptTy e then i + 1 else i
  match e with
  | .app f a => let (s, r, i) := scanTerm f seen r i; scanTerm a s r i
  | .lam _ d b _ => let (s, r, i) := scanTerm d seen r i; scanTerm b s r i
  | .forallE _ d b _ => let (s, r, i) := scanTerm d seen r i; scanTerm b s r i
  | .letE _ t v b _ =>
      let (s, r, i) := scanTerm t seen r i
      let (s, r, i) := scanTerm v s r i
      scanTerm b s r i
  | .mdata _ b => scanTerm b seen r i
  | .proj _ _ b => scanTerm b seen r i
  | _ => (seen, r, i)

def expectedLedgerTally : String := "rows=21 res=124"

/-- The rows, machine-produced, sorted by `res` then `prem` descending.  One
    row carries the item's sharpest number: `flowNode_toKey` holds **65** of
    the remaining **124** residue sites, and its own five callees hold five
    more.  Three rows are all-zero — the proof never reaches the right arm by
    any route — and two of those three are PROJECTIONS, so their "conclusion"
    is a park FIELD and narrowing it is the supply-side operation items
    212-218 priced, not this one. -/
def expectedLedger : List String :=
  ["res=65 imp=115 prem=0 proj=0 FlowKeyLift.flowNode_toKey",
   "res=11 imp=100 prem=6 proj=0 flowKeyRoute_of_root",
   "res=10 imp=85 prem=2 proj=0 flowKeyRoute_of_open",
   "res=9 imp=61 prem=3 proj=0 resumectx_of_landing",
   "res=4 imp=7 prem=1 proj=0 markerctx_of_landing",
   "res=4 imp=7 prem=1 proj=0 suffixctx_of_landing",
   "res=4 imp=12 prem=0 proj=0 FlowKeyLift.flowContent_toBlockKey",
   "res=3 imp=10 prem=2 proj=0 dedent_cover_of_landing",
   "res=3 imp=5 prem=1 proj=0 flowOpen_stamp",
   "res=3 imp=12 prem=0 proj=0 keyctx_of_preprocess",
   "res=3 imp=12 prem=0 proj=0 nodocctx_of_preprocess",
   "res=1 imp=4 prem=2 proj=0 explFrameValueLine",
   "res=1 imp=3 prem=1 proj=0 flowVPack_of_close",
   "res=1 imp=4 prem=1 proj=0 PreprocessIndentStable.IndentFloor.transport",
   "res=1 imp=4 prem=1 proj=0 flowOpen_floor_at_prep",
   "res=1 imp=7 prem=0 proj=0 FlowKeyLift.props_toKey",
   "res=0 imp=8 prem=2 proj=0 frameChainUnion",
   "res=0 imp=0 prem=0 proj=0 FlowKeyLift.flowNode_toBlockKey",
   "res=0 imp=0 prem=0 proj=0 flowKeyHead",
   "res=0 imp=0 prem=0 proj=1 FlowBaseRoutes.key",
   "res=0 imp=0 prem=0 proj=1 FlowBaseRoutes.vslot"]

/-! ## §4 What stops the other five

`flowNode_toKey`'s residue arises at an INTERIOR span and its conclusion is
about the OUTER one, so the only proposition that could carry it out is one
about the SPAN — "the characters between `s` and `s'` contain a break".  Saying
that needs `s'.chars` to be a suffix of `s.chars` for every production in the
flow grammar, and this counts what that would take: the mutual block's size,
and how many such lemmas the library already has. -/

def expectedFamily : String := "types=18 ctors=69 suffixLemmas=0"

open Meta in
run_cmd do
  let env ← getEnv
  let stx ← `(term| Or.inr trivial)
  let mut rows : Array (Nat × Nat × String) := #[]
  let mut tot := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    match ci with | .thmInfo _ => pure () | _ => continue
    let ok ← liftTermElabM do
      forallTelescope ci.type fun _ concl => do
        if !(← inferType concl).isProp then return false
        provableBy stx concl
    if !ok then continue
    let v := ci.value? (allowOpaque := true) |>.getD (mkConst ``True.intro)
    let (_, r, i) := scanTerm v {} 0 0
    let prem := (optBinders ci.type).1.size
    let proj := if (env.getProjectionFnInfo? nm).isSome then 1 else 0
    tot := tot + r
    rows := rows.push (r, prem, s!"res={r} imp={i} prem={prem} proj={proj} {shortName nm}")
  let got := s!"rows={rows.size} res={tot}"
  if got != expectedLedgerTally then
    throwError "the obligation tally moved.\nexpected: {expectedLedgerTally}\ngot:      {got}"
  let gotRows := (rows.qsort (fun a b =>
    if a.1 != b.1 then a.1 > b.1
    else if a.2.1 != b.2.1 then a.2.1 > b.2.1
    else a.2.2 < b.2.2)).map (·.2.2)
  if gotRows.toList != expectedLedger then
    throwError "the obligation ledger moved.  Paste-ready:\n{
      String.intercalate "\n" (gotRows.map (fun r => "   \"" ++ r ++ "\",")).toList}"
  -- §4: the mutual block the family narrowing would have to walk, and how
  -- many of its productions the library can already relate to a suffix.
  let some (.inductInfo fi) := env.find? ``L4YAML.Surface.SFlowNode
    | throwError "the flow grammar's head type is gone"
  let mut ctors := 0
  for t in fi.all do
    match env.find? t with
    | some (.inductInfo g) => ctors := ctors + g.ctors.length
    | _ => pure ()
  let mut sfx := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    match ci with | .thmInfo _ => pure () | _ => continue
    let us := ci.type.getUsedConstants
    if (fi.all.any (us.contains ·)) && us.contains ``List.IsSuffix then sfx := sfx + 1
  let gotF := s!"types={fi.all.length} ctors={ctors} suffixLemmas={sfx}"
  if gotF != expectedFamily then
    throwError "the flow family moved.\nexpected: {expectedFamily}\ngot:      {gotF}"

end Tests.Guards.ConclusionObligationCensus
