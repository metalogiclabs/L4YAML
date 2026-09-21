/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML
import L4YAML.Proofs.Production.FlowKeyLift

/-!
# The span instrument, measured (DOCS item 229)

Item 228 priced the suffix lemma for `Surface/Node.lean`'s mutual block by
SIGNATURES, before a line of it existed: **69 constructor arms**.  This file
re-derives that number and the one the price missed.

§1 walks the closure of production types reachable from the block and counts
what a suffix family actually has to cover.  §2 counts how much of the closure
the library now relates to `List.IsSuffix`.  §3 pins the eighteen mutual-block
lemmas by name.  §4 sorts the four residues of `Proofs.FlowKeyLift` by the
only question a narrowing's worth turns on — can a consumer refute it.

The discipline these pins carry: **a price taken by signatures prices the
thing it counted, not the thing that has to be built**.  69 is right about the
block and is 48% of the arms the instrument needed.
-/

set_option autoImplicit false

namespace Tests.Guards.SurfaceSpanCensus

open Lean Elab Command Meta
open L4YAML.Surface
open L4YAML.Proofs.SurfaceSpan

/-! ## §0 The instrument is not vacuous

A suffix lemma over an uninhabited family is true and worth nothing, and this
tree has had constructors that nothing ever instantiated (DOCS items 33, 107).
So the family is exercised on a derivation first: `[]`, the empty flow
sequence, read as `[161] ns-flow-node(0, flow-out)`, and the instrument
applied to it. -/

/-- A real derivation in the mutual block. -/
example (rest : List Char) (col : Nat) :
    SFlowNode 0 .flowOut ⟨'[' :: ']' :: rest, col⟩ ⟨rest, col + 2⟩ :=
  SFlowNode.content 0 .flowOut _ _
    (SFlowContent.flowSeq 0 .flowOut _ _
      (SFlowSequence.empty 0 .flowOut _ _ _ _
        (GLit.mk _ _) (GOpt.none _) (GLit.mk _ _)))

/-- …and `sFlowNode_suffix` on it: the two brackets are the span. -/
example (rest : List Char) (col : Nat) : rest <:+ '[' :: ']' :: rest :=
  sFlowNode_suffix (SFlowNode.content 0 .flowOut _ _
    (SFlowContent.flowSeq 0 .flowOut _ _
      (SFlowSequence.empty 0 .flowOut ⟨'[' :: ']' :: rest, col⟩ _ _ ⟨rest, col + 2⟩
        (GLit.mk _ _) (GOpt.none _) (GLit.mk _ _))))

/-! ## §1 The closure the instrument had to cover

A "production" is any constant whose type ends `… → SurfPos → SurfPos → Prop`.
The walk starts at the mutual block and follows constructor types AND def
bodies — the first version of this census followed only inductives and read
**48** types, because `[69] s-separate(n,c)`, `[131] ns-plain(n,c)` and eleven
others are `def`s that dispatch on the context.  A closure walk that stops at
a definition under-reports the thing it is pricing. -/

def expectedClosure : String :=
  "types=74 ind=61 def=13 ctors=143 block=18/69 leaf=56/74"

/-- Every production type reachable from `SFlowNode`'s mutual block, with its
    constructor count (0 for a `def`) and whether it is in the block. -/
def productionClosure (env : Environment) : MetaM (Array (Name × String × Nat × Bool)) := do
  let shape (nm : Name) : MetaM (Option (String × Nat)) := do
    let some ci := env.find? nm | return none
    forallTelescope ci.type fun xs cod => do
      if !cod.isProp then return none
      if xs.size < 2 then return none
      let t1 ← inferType xs[xs.size-1]!
      let t2 ← inferType xs[xs.size-2]!
      if !(t1.isConstOf ``SurfPos && t2.isConstOf ``SurfPos) then return none
      match ci with
      | .inductInfo fi => return some ("ind", fi.ctors.length)
      | .defnInfo _ => return some ("def", 0)
      | _ => return none
  let some (.inductInfo root) := env.find? ``SFlowNode
    | throwError "the flow grammar's head type is gone"
  let mut seen : Std.HashSet Name := {}
  let mut work : List Name := root.all
  let mut rows : Array (Name × String × Nat × Bool) := #[]
  while !work.isEmpty do
    let nm := work.head!
    work := work.tail!
    if seen.contains nm then continue
    match ← shape nm with
    | none => continue
    | some (kind, nc) =>
      seen := seen.insert nm
      rows := rows.push (nm, kind, nc, root.all.contains nm)
      let some ci := env.find? nm | continue
      let mut next : Array Name := #[]
      match ci with
      | .inductInfo fi =>
        for ctor in fi.ctors do
          if let some cci := env.find? ctor then next := next ++ cci.type.getUsedConstants
      | _ =>
        if let some v := ci.value? (allowOpaque := true) then next := next ++ v.getUsedConstants
      for u in next do
        if !seen.contains u then work := u :: work
  return rows

/-! ## §2 How much of it the library relates to a suffix

The same reading item 228's `ConclusionObligationCensus` §4 takes, widened
from the 18 to the whole closure: a type is covered when some theorem's TYPE
mentions both it and `List.IsSuffix`.  At item 228 this read 10 of 74 — the
comment family in `Proofs/Coupling/TabIndentBridge.lean`. -/

/-- 69 of the 74; the five that never appear in a suffix lemma's TYPE are
    `abbrev`s — `SBAsLineFeed` and `SBNonContent` are `[28] b-break`, and
    `SNbChar`, `SNsChar`, `SCommentChar` are `GChar` at three predicates — so
    `sbBreak_suffix` and `gchar_suffix` cover them definitionally and a second
    statement would be a second name for the same fact. -/
def expectedCoverage : String := "closure=74 covered=69 uncovered=5"

/-! ## §3 The mutual block's eighteen -/

def expectedBlockLemmas : List String :=
  ["sBlockIndented_suffix",
   "sBlockMapEntries_suffix",
   "sBlockMapEntry_suffix",
   "sBlockNode_suffix",
   "sBlockSeqEntries_suffix",
   "sCompactMapTail_suffix",
   "sCompactMap_suffix",
   "sCompactSeqTail_suffix",
   "sCompactSeq_suffix",
   "sFlowContent_suffix",
   "sFlowMapEntries_suffix",
   "sFlowMapEntry_suffix",
   "sFlowMapping_suffix",
   "sFlowNode_suffix",
   "sFlowSeqEntries_suffix",
   "sFlowSeqEntry_suffix",
   "sFlowSequence_suffix",
   "sImplicitKey_suffix"]

run_cmd liftTermElabM do
  let env ← getEnv
  let rows ← productionClosure env
  let inds := rows.filter (·.2.1 == "ind")
  let defs := rows.filter (·.2.1 == "def")
  let inB := rows.filter (·.2.2.2)
  let ctorsAll := rows.foldl (fun a r => a + r.2.2.1) 0
  let ctorsIn := inB.foldl (fun a r => a + r.2.2.1) 0
  let got := s!"types={rows.size} ind={inds.size} def={defs.size} ctors={ctorsAll} \
block={inB.size}/{ctorsIn} leaf={rows.size - inB.size}/{ctorsAll - ctorsIn}"
  if got != expectedClosure then
    throwError "the production closure moved.\nexpected: {expectedClosure}\ngot:      {got}"
  -- §2
  let names : Std.HashSet Name := rows.foldl (fun a r => a.insert r.1) {}
  let mut covered : Std.HashSet Name := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    match ci with | .thmInfo _ => pure () | _ => continue
    let us := ci.type.getUsedConstants
    if !us.contains ``List.IsSuffix then continue
    for t in us do
      if names.contains t then covered := covered.insert t
  let gotC := s!"closure={rows.size} covered={covered.size} uncovered={rows.size - covered.size}"
  if gotC != expectedCoverage then
    throwError "the suffix coverage moved.\nexpected: {expectedCoverage}\ngot:      {gotC}\n\
uncovered: {(rows.filterMap (fun r => if covered.contains r.1 then none else some r.1.toString)).qsort (· < ·)}"
  -- §3
  let blockLemmas := (rows.filter (·.2.2.2)).filterMap fun r =>
    let lem := (`L4YAML.Proofs.SurfaceSpan).str (r.1.getString!.decapitalize ++ "_suffix")
    if (env.find? lem).isSome then some lem.getString! else none
  let gotB := (blockLemmas.qsort (· < ·)).toList
  if gotB != expectedBlockLemmas then
    throwError "the block's suffix lemmas moved.  Paste-ready:\n{
      String.intercalate "\n" (blockLemmas.qsort (· < ·) |>.map (fun r => "   \"" ++ r ++ "\",")).toList}"

/-! ## §4 The four residues, sorted by refutability

`conclusion_eliminable_iff` (item 228) says a narrowed conclusion `A ∨ R`
yields `A` exactly when the consumer can refute `R`.  These four are
`Proofs.FlowKeyLift`'s residues; the question is settled for all four, and the
answers differ. -/

open L4YAML.Proofs.FlowKeyLift in
/-- Three carry a break in their own span, and so are refutable by a
    single-line consumer. -/
example {n : Nat} {c : L4YAML.YamlContext} {s s' : SurfPos} :
    (PlainResidue n c s s' → BreakBetween s s') ∧
    (DoubleResidue n s s' → BreakBetween s s') ∧
    (SingleResidue n s s' → BreakBetween s s') :=
  ⟨plainResidue_break, doubleResidue_break, singleResidue_break⟩

open L4YAML.Proofs.FlowKeyLift in
/-- The fourth is not, and the reason is that its span can be EMPTY: no
    predicate on the characters between the two positions separates it from a
    separation that was never taken. -/
example (chars : List Char) :
    SepResidue 0 ⟨chars, 0⟩ ⟨chars, 0⟩ ∧ ¬ BreakBetween ⟨chars, 0⟩ ⟨chars, 0⟩ :=
  sepResidue_span_can_be_empty chars

/-! ## §5 Where the 83 dead sites actually go

Item 228's FALSE probe read **83** compiler errors for `flowNode_toKey` and
its NEXT called the suffix lemma "the one thing that would turn 83 dead sites
into 83 payable ones".  The lemma exists now, and that sentence is wrong: a
site is payable when the leaf it declines through carries a REFUTABLE residue,
and the four leaves are not alike.

(The two numbers below are 82, not 83.  They are a different instrument —
occurrences of `@Or.inr _ True _` in the proof term, against a count of errors
after rewriting the conclusion — and neither corrects the other; item 228's
own instrument debt records that an error count is a property of how a proof
is written.)

This counts the leaf applications in `flowNode_toKey`'s own proof TERM — not
its source text, so the number survives a re-indent — and splits them by
whether §4's break argument reaches that leaf.  `sep_toKey` and `sepOpt_toKey`
relay `SepResidue`, whose span can be empty; `props_toKey` relays `sep_toKey`.
One residue of the four blocks the overwhelming majority. -/

def expectedLeafSplit : String :=
  "noop=82 payable=3 blocked=45 relay=34"

/-- How many times a constant occurs in a term, WITHOUT deduplication: the
    compiler pays per occurrence, and item 228's DAG walk undercounted for
    exactly this reason. -/
partial def countConst (target : Name) (e : Expr) : Nat :=
  (if e.isConstOf target then 1 else 0) + sub e
where
  sub (e : Expr) : Nat :=
    match e with
    | .app f a => countConst target f + countConst target a
    | .lam _ d b _ => countConst target d + countConst target b
    | .forallE _ d b _ => countConst target d + countConst target b
    | .letE _ t v b _ => countConst target t + countConst target v + countConst target b
    | .mdata _ b => countConst target b
    | .proj _ _ b => countConst target b
    | _ => 0

/-- The dead sites themselves: `@Or.inr _ True _`, counted per occurrence.
    Selecting on the right disjunct's TYPE and not on the witness matters —
    only 28 of the 82 carry a syntactic `True.intro`. -/
partial def countNoop (e : Expr) : Nat :=
  (if e.isAppOfArity ``Or.inr 3 && (e.getArg! 1).isConstOf ``True then 1 else 0) +
  match e with
  | .app f a => countNoop f + countNoop a
  | .lam _ d b _ => countNoop d + countNoop b
  | .forallE _ d b _ => countNoop d + countNoop b
  | .letE _ t v b _ => countNoop t + countNoop v + countNoop b
  | .mdata _ b => countNoop b
  | .proj _ _ b => countNoop b
  | _ => 0

run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? ``L4YAML.Proofs.FlowKeyLift.flowNode_toKey
    | throwError "flowNode_toKey is gone"
  let some v := ci.value? (allowOpaque := true) | throwError "no proof term"
  let n (s : String) := countConst ((`L4YAML.Proofs.FlowKeyLift).str s) v
  let noop := countNoop v
  let payable := n "plain_toKey" + n "doubleQuoted_toKey" + n "singleQuoted_toKey"
  let blocked := n "sep_toKey" + n "sepOpt_toKey" + n "props_toKey"
  -- what is left declines through the recursion itself, so it follows the
  -- worst leaf its sub-derivation reaches.
  let relay := noop - payable - blocked
  let got := s!"noop={noop} payable={payable} blocked={blocked} relay={relay}"
  if got != expectedLeafSplit then
    throwError "the leaf split moved.\nexpected: {expectedLeafSplit}\ngot:      {got}"

end Tests.Guards.SurfaceSpanCensus
