/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ProducerDerivation

/-!
# What a dispatch equation buys (DOCS item 242)

Item 241 refuted derivability at the park's producer: a `ScannerSurfCorr` is a
statement about a POINT and the datum `SLYamlStream sp_start sp_scan'` is a
statement about a PATH, and the library turns one into the other at the stream's
seed and nowhere else.  Its recorded NEXT named the four consumers as holding
what the producer does not — a dispatch equation and a second correspondence,
at the position BEFORE the step — and called that pair the first thing in the
chain that could turn a point into a path.

**Three of those four hold no dispatch equation.**
`block_dispatch_deferred_inline`, `…_stamp_nopack` and `…_stamp_offcol` carry
branch evidence — `_h_src`, `_h_indent`, `_h_ne`, `_h_park`, `_h_res` — and pass
the producer's own five arguments straight through.  `accum_content_pending` is
the one that holds `scanNextToken_dispatchContent … = .ok s'`, and its second
correspondence is its CONCLUSION rather than a hypothesis.  So the census below
is taken over the whole population instead of over that ring.

## The answer: availability is 294 and derivation is 1

§2 reads every authored statement for a scanner step equation `f … = .ok …`
and for a grammar path landing on the position the step's output names.

| rung | what it asks | count |
|---|---|---|
| `dispHolders` | a `scanNextToken_dispatch*` equation is held | **294** |
| `dispTwoCorr` | …with two correspondences beside it | **28** |
| `edge` | a production LANDS on the step's output position | **4** |
| `chain` | a production path RUNS from a known point to it | **1** |

The one is `indentedValue_reads_at_any_indent`, and per FUNCTION the reading is
sharper still: of **72** distinct scanner step functions appearing in step
equations, **one** carries a numbered spec production across it and **two**
carry any Surface relation at all — `scanNextToken_preprocess` (6 of its 186
holders) and `scanNextToken_dispatchContent` (1 of its 129).  The step that
consumes SEPARATION is grammar-visible and routine; the step that consumes
CONTENT is grammar-visible once.  **A census that counts equations measures
availability, and the two numbers are 294 and 1.**

`indentedValue_reads_at_any_indent` is in neither item 238's transitive set nor
either repair thread, so the one worked precedent stands outside β.5's bill.

## And the escape's repaired form needs no arm at all

`SLYamlStream.scannerDrop` takes a stream to `s₁` and an `SSLComments` from an
unrelated `s₂`, which is what makes it hold of every string.  §1 proves that
**connecting the two halves makes the arm redundant**: given `SLYamlStream a b`
and `SSLComments b c`, `SLYamlStream a c` follows from `implicitContinue`,
`SLDocumentPrefix.comments` and the fact that an `s-b-comment` is an
`l-comment`.  `connected_drop_nd` proves the same in item 239's post-β.5 model,
where the arm is gone, so the derivation is not circular — and the pin below
checks that neither proof mentions `SLYamlStream.scannerDrop`.

**So the grammar side of β.5 is three lines, and the whole bill is the
connection.**  What items 240 and 241 priced — nineteen statements threading a
premise through `close_with_ssl`, or eighteen through the producer — is not the
cost of proving the step; it is the cost of establishing that the production
starts where the stream ends.

**The derivation leans on a documented deviation from the spec.**  [66]
`s-separate-in-line` is `s-white+ | <start-of-line>`, and
`SSeparateInLine.startOfLine` holds at EVERY position in this library
(`L4YAML/Surface/Basic.lean`, which records the weakening and the ~20 proof
sites it was taken to avoid).  `ssb_to_slcomment`'s `noSep` branch spends
exactly that, and the pin below records the dependency rather than leaving it
to a reader.  Under the spec's own column restriction the branch would need the
comment run to begin at column 0.
-/

namespace Tests.Guards.DispatchPrice

open Lean Lean.Meta Lean.Elab
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML (getYamlSpecRefs)
open Tests.Guards.DropFalsity (StreamND)
open Tests.Guards.DropDependents (usesAll census modOf sorted)
open Tests.Guards.RepairChoice (revEdges thread producer supplier)

/-! ## §1 The connected escape -/

lemma ssb_to_slcomment {a b : SurfPos} (h : SSBComment a b) : SLComment a b := by
  cases h
  case withSep =>
    rename_i s₁ s₂ hsep hopt hb
    exact SLComment.mk _ s₁ s₂ _ hsep hopt hb
  case noSep =>
    rename_i hb
    exact SLComment.mk _ _ _ _ (SSeparateInLine.startOfLine _) (GOpt.none _) hb

lemma sslcomments_to_prefix {a b : SurfPos} (h : SSLComments a b) :
    SLDocumentPrefix a b := by
  cases h
  case withComment =>
    rename_i s₁ hsb hstar
    exact SLDocumentPrefix.comments _ _ (GStar.cons _ s₁ _ (ssb_to_slcomment hsb) hstar)
  case startOfLine =>
    rename_i chars hstar
    exact SLDocumentPrefix.comments _ _ hstar

lemma connected_drop {a b c : SurfPos}
    (h : SLYamlStream a b) (hc : SSLComments b c) : SLYamlStream a c :=
  SLYamlStream.implicitContinue a b c c c h
    (GStar.cons b c c (sslcomments_to_prefix hc) (GStar.nil c))
    (GOpt.none c) (GStar.nil c)

lemma connected_drop_nd {a b c : SurfPos}
    (h : StreamND a b) (hc : SSLComments b c) : StreamND a c :=
  StreamND.implicitContinue a b c c c h
    (GStar.cons b c c (sslcomments_to_prefix hc) (GStar.nil c))
    (GOpt.none c) (GStar.nil c)

/-! ## §2 The census -/

def isProd (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  forallTelescope ci.type fun xs concl => do
    unless concl == mkSort Level.zero do return false
    if xs.size < 2 then return false
    return (← inferType xs[xs.size-2]!).isConstOf ``SurfPos
      && (← inferType xs[xs.size-1]!).isConstOf ``SurfPos

partial def scanAux (prods : Std.HashSet Name) (e : Expr) :
    StateM (Std.HashSet Expr × Array (Name × Expr × Expr) × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (s, a, b) => (s.insert e, a, b)
  if let .const n _ := e.getAppFn then
    if prods.contains n then
      let args := e.getAppArgs
      if args.size ≥ 2 then
        modify fun (s, a, b) => (s, a.push (n, args[args.size-2]!, args[args.size-1]!), b)
  if e.isAppOfArity ``ScannerSurfCorr 2 then
    modify fun (s, a, b) => (s, a, b.push e.appArg!)
  let _ ← e.foldlM (fun (_ : Unit) s => scanAux prods s) ()

def scanE (prods : Std.HashSet Name) (e : Expr) :
    Array (Name × Expr × Expr) × Array Expr :=
  let (_, a, b) := ((scanAux prods e).run ({}, #[], #[])).2
  (a, b)

def stepEqFn? (t : Expr) : Option Name := do
  guard (t.isAppOfArity ``Eq 3)
  let lhs := t.appFn!.appArg!
  guard (t.appArg!.isAppOf ``Except.ok)
  let .const f _ := lhs.getAppFn | none
  guard ((`L4YAML.Scanner).isPrefixOf f)
  some f

partial def fvarsAux (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (s, a) => (s.insert e, a)
  if e.isFVar then modify fun (s, a) => (s, a.push e)
  let _ ← e.foldlM (fun (_ : Unit) s => fvarsAux s) ()

def okStates (t : Expr) : MetaM (Array Expr) := do
  let vs := ((fvarsAux t.appArg!).run ({}, #[])).2.2
  vs.filterM fun v => return (← inferType v).isConstOf ``ScannerState

structure R where
  fns      : Array Name := #[]
  edgeFns  : Array Name := #[]
  chainFns : Array Name := #[]
  twoCorr  : Bool := false
deriving Inhabited

def readDecl (prods : Std.HashSet Name) (n : Name) : MetaM R := do
  let some ci := (← getEnv).find? n | return {}
  forallTelescope ci.type fun xs concl => do
    let (pc, _) := scanE prods concl
    let mut fns : Array Name := #[]
    let mut posts : Array (Name × Expr) := #[]
    let mut corrHyps : Array Expr := #[]
    let mut corrAt : Array (Expr × Expr) := #[]
    let mut pAll := pc
    for x in xs do
      let t ← inferType x
      if let some f := stepEqFn? t then
        fns := fns.push f
        for st in ← okStates t do posts := posts.push (f, st)
      if t.isAppOfArity ``ScannerSurfCorr 2 then
        corrHyps := corrHyps.push t.appArg!
        corrAt := corrAt.push (t.appFn!.appArg!, t.appArg!)
      pAll := pAll ++ (scanE prods t).1
    let reach (src : Expr) : Std.HashSet Expr := Id.run do
      let mut seen : Std.HashSet Expr := {src}
      let mut todo : List Expr := [src]
      while !todo.isEmpty do
        let x := todo.head!
        todo := todo.tail!
        for (_, a, b) in pAll do
          if a == x && !seen.contains b then
            seen := seen.insert b
            todo := b :: todo
      return seen
    let mut edgeFns : Array Name := #[]
    let mut chainFns : Array Name := #[]
    for (f, st) in posts do
      for (s, p) in corrAt do
        if s == st then
          if pAll.any (fun (_, _, b) => b == p) then edgeFns := edgeFns.push f
          if corrHyps.any (fun q => q != p && (reach q).contains p) then
            chainFns := chainFns.push f
    return { fns := fns, edgeFns := edgeFns, chainFns := chainFns,
             twoCorr := corrHyps.size ≥ 2 }

/-! ## §3 The pins -/

/-- The grammar's alphabet over surface positions, three nested populations.
    `prodTyped` takes every relation whose last two arguments are `SurfPos` and
    so includes the proof layer's own composites (`PendingNode`, `BlockStack`,
    `ImplicitKeyHead`, `PropsRun`); `prodSurf` keeps the `L4YAML/Surface`
    modules, which are the spec transcription and its combinators; `prodSpec`
    keeps only what carries a NUMBERED `@[yaml_spec]` rule.  A combinator
    application like `GStar SSWhite` is headed by `GStar`, which carries no rule
    number of its own, which is why `prodSurf` and not `prodSpec` is the
    population the findings are read over. -/
def expectedAlphabet : String := "prodTyped=129 prodSurf=92 prodSpec=54"

/-- The step population, which no choice of grammar moves: 1646 statements hold
    a scanner step equation, 294 of them a dispatch equation, and 28 of those
    hold it with two correspondences — the pair item 241's NEXT called the first
    thing that could turn a point into a path.  Of the 72 step functions, 26 are
    the indexed twin's. -/
def expectedSteps : String :=
  "stepHolders=1646 dispHolders=294 dispTwoCorr=28 fns=72 fnsIx=26"

/-- **The ladder, at each population.**  `edge` is a production whose right
    endpoint is the step's output; `chain` requires a path to it from another
    correspondence's position, existential midpoints allowed — which is what
    `implicitKeyHead_of_dispatch` needs and a single edge misses.  The counts
    fall 294 → 28 → 18 → 6 → 1 as the question tightens from availability to
    derivation. -/
def expectedLadder : List String :=
  ["TYPED edge=20 chain=7 fnEdge=3 fnChain=2",
   "SURF edge=18 chain=6 fnEdge=2 fnChain=2",
   "SPEC edge=4 chain=1 fnEdge=2 fnChain=1"]

/-- The six that carry a Surface path across a scanner step.  Five are
    preprocessing's; the sixth holds both equations, which is why the per
    function counts (6 and 1) sum to more than the six declarations here. -/
def expectedChainSurf : List Name :=
  [`L4YAML.Proofs.StreamAccum.SSeparateLines_at_interior,
   `L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent,
   `L4YAML.Proofs.StreamAccum.keyctx_of_preprocess,
   `L4YAML.Proofs.StreamAccum.preprocess_flow_thread,
   `L4YAML.Proofs.StreamAccum.tab_refutes_dispatch,
   `L4YAML.Proofs.StreamAccum.tab_refutes_dispatch_inline]

/-- **And the one that carries a NUMBERED production across a content
    dispatch.**  Its conclusion pairs `SSeparateLines n sp_scan sp_prep` with a
    node reading from `sp_prep` to the dispatch's own output. -/
def expectedChainSpec : List Name :=
  [`L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent]

/-- The two functions, with how many of their holders carry the path. -/
def expectedPerFn : List String :=
  ["scanNextToken_dispatchContent decls=129 chain=1",
   "scanNextToken_preprocess decls=186 chain=6"]

/-- **The one worked precedent is outside the work.**  It is not in item 238's
    transitive set and not on either repair thread, so β.5 neither pays for it
    nor inherits it. -/
def expectedOne : String := "inT=false onThread=false onProdThread=false"

/-- **What §1's derivation spends and what it does not.**  `startOfLine=true`
    records the deviation from [66] the `noSep` branch rides on;
    `drop=false` is the non-circularity check — a proof that the escape is
    redundant may not route through the escape. -/
def expectedWeak : String := "startOfLine=true drop=false"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let pre := usesAll env
  let (authored, usesVal) := pre
  -- §2a the alphabet
  let mut prodTyped : Std.HashSet Name := {}
  let mut prodSurf : Std.HashSet Name := {}
  let mut prodSpec : Std.HashSet Name := {}
  for n in authored do
    if ← isProd n then
      prodTyped := prodTyped.insert n
      if (`L4YAML.Surface).isPrefixOf (modOf env n) then prodSurf := prodSurf.insert n
      if (getYamlSpecRefs env n).any (fun r => r.rule.isSome) then prodSpec := prodSpec.insert n
  let gotA := s!"prodTyped={prodTyped.size} prodSurf={prodSurf.size} prodSpec={prodSpec.size}"
  unless gotA == expectedAlphabet do
    throwError "the grammar alphabet moved:\n  got      {gotA}\n  expected {expectedAlphabet}"
  -- §2b the ladder, at each population
  let mut ladder : Array String := #[]
  let mut perFn : Array String := #[]
  let mut steps := ""
  let mut chainSurf : Array Name := #[]
  let mut chainSpec : Array Name := #[]
  for (tag, prods) in [("TYPED", prodTyped), ("SURF", prodSurf), ("SPEC", prodSpec)] do
    let mut stepHolders : Nat := 0
    let mut dispHolders : Nat := 0
    let mut dispTwoCorr : Nat := 0
    let mut edgeN : Nat := 0
    let mut chainN : Array Name := #[]
    let mut fnsAll : Std.HashSet Name := {}
    let mut fnsEdge : Std.HashSet Name := {}
    let mut fnsChain : Std.HashSet Name := {}
    let mut declByFn : Std.HashMap Name Nat := {}
    let mut chainByFn : Std.HashMap Name (Array Name) := {}
    for n in authored do
      let r ← readDecl prods n
      if r.fns.isEmpty then continue
      stepHolders := stepHolders + 1
      for f in r.fns do
        fnsAll := fnsAll.insert f
        declByFn := declByFn.insert f (declByFn.getD f 0 + 1)
      if r.fns.any (fun f => "scanNextToken_dispatch".isPrefixOf f.getString!) then
        dispHolders := dispHolders + 1
        if r.twoCorr then dispTwoCorr := dispTwoCorr + 1
      for f in r.edgeFns do fnsEdge := fnsEdge.insert f
      for f in r.chainFns do
        fnsChain := fnsChain.insert f
        chainByFn := chainByFn.insert f ((chainByFn.getD f #[]).push n)
      if !r.edgeFns.isEmpty then edgeN := edgeN + 1
      if !r.chainFns.isEmpty then chainN := chainN.push n
    let ixN := (fnsAll.toArray.filter (`L4YAML.Scanner.Indexed).isPrefixOf).size
    steps := s!"stepHolders={stepHolders} dispHolders={dispHolders} \
dispTwoCorr={dispTwoCorr} fns={fnsAll.size} fnsIx={ixN}"
    ladder := ladder.push s!"{tag} edge={edgeN} chain={chainN.size} \
fnEdge={fnsEdge.size} fnChain={fnsChain.size}"
    if tag == "SURF" then
      chainSurf := sorted chainN
      for f in sorted fnsChain.toArray do
        perFn := perFn.push s!"{f.getString!} decls={declByFn.getD f 0} \
chain={(chainByFn.getD f #[]).size}"
    if tag == "SPEC" then chainSpec := sorted chainN
  unless steps == expectedSteps do
    throwError "the step population moved:\n  got      {steps}\n  expected {expectedSteps}"
  unless ladder.toList == expectedLadder do
    throwError "the ladder moved:\n  got      {ladder.toList}\n  expected {expectedLadder}"
  unless chainSurf.toList == expectedChainSurf do
    throwError "the Surface chain-carriers moved: {chainSurf.toList}"
  unless chainSpec.toList == expectedChainSpec do
    throwError "the spec chain-carrier moved: {chainSpec.toList}"
  unless perFn.toList == expectedPerFn do
    throwError "the per-function reading moved:\n  got      {perFn.toList}\n  \
expected {expectedPerFn}"
  -- §4 where the one precedent sits
  let c ← census (some pre)
  let rev := revEdges authored usesVal
  let one := `L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent
  let gotO := s!"inT={c.trans.contains one} onThread={(thread rev supplier).contains one} \
onProdThread={(thread rev producer).contains one}"
  unless gotO == expectedOne do
    throwError "the precedent moved:\n  got      {gotO}\n  expected {expectedOne}"
  -- §5 what §1's derivation spends
  let usedBy (n : Name) : Array Name :=
    match env.find? n with
    | none => #[]
    | some ci => ((ci.value? (allowOpaque := true)).getD (mkConst n)).getUsedConstants
  let deps := usedBy ``connected_drop ++ usedBy ``connected_drop_nd
    ++ usedBy ``sslcomments_to_prefix ++ usedBy ``ssb_to_slcomment
  let gotW := s!"startOfLine={deps.contains ``SSeparateInLine.startOfLine} \
drop={deps.contains ``SLYamlStream.scannerDrop}"
  unless gotW == expectedWeak do
    throwError "the derivation's dependencies moved:\n  got      {gotW}\n  \
expected {expectedWeak}"
  logInfo m!"DispatchPrice {gotA} {steps} {ladder.toList} {gotO} {gotW}"

end Tests.Guards.DispatchPrice
