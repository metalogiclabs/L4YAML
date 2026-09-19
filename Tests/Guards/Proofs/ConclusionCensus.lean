import L4YAML.Proofs.Production.StreamAccum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The census over CONCLUSIONS (DOCS item 201)

Item 198 ran a census over the pending park's CONSTRUCTORS, asking which of
them carried both bottoms; item 200 ran one over their APPLICATION SITES,
asking which sites paid a field and punted its own weakening.  Both items
recorded, in the same words, the row neither could reach:

> Both censuses run over the park family.  Neither runs over lemma
> CONCLUSIONS, so `flowKeyRoute_of_root` — which carries a value-line-bottomed
> resume conjunct and punts it — is still unmeasured.  **A census over
> conclusions is the instrument that would find it, and nobody has built one.**

This is that instrument.  For every non-internal constant of
`L4YAML/Proofs/Production/StreamAccum.lean`, split the TYPE into its binder
telescope and its conclusion, collect the `_ ∨ True` components of the
CONCLUSION, and read the VALUE for an `Or.inl` and an `Or.inr` of each.  A
conjunct with no `Or.inl` anywhere in the proof is one no arm of that lemma
ever pays — which is a different question from "is this field punted at some
site", and is the one the park censuses cannot ask.

**What it reads.**  16 lemmas state an optional conjunct in their conclusion,
24 conjuncts between them — of which **15 have a paying arm and 9 have none**
(13 and 11 at item 200's `123e3313`).  Three lemmas carry more than one, and they are the
same lemma seen three ways: `flowKeyRoute_of_open` (5), `flowKeyRoute_of_root`
(5) and the field that carries both (`FlowBaseRoutes.key`, 5, excluded below as
a projection).  **Conclusion-level optionality in this module is the flow-key
lane and nothing else.**

**Both blind spots, named.**  An instrument that counts syntax misses what
syntax hides, and this one misses two things in opposite directions:

* A conjunct **relayed** with `Or.imp` (`h.imp f id`) writes no literal
  `Or.inl` or `Or.inr`, so it reads `inl=0 inr=0` — neither paid nor punted.
  `flowKeyHead`, `back_col`, `close_col_of_base` and `scanValue_ok_park_facts`
  are exactly that, and all four DO pay.  This is the same blind spot item 199
  measured in the `[210]` flip, in a second instrument: **a relay is invisible
  to anything that counts terms**, because it writes the answer down once and
  the writing is not at either end.
* `inr` counts punt SITES, not "always punted".  A payment that keeps a
  fallback arm — every payment made through a `match` on an optional premise —
  leaves the `inr` count exactly where it was.  Item 201's own payment moved
  `flowKeyRoute_of_root`'s two rows `inl=0 → inl=1` and `inr=2 → inr=2`.

So the number to read is the FIRST column, and the gate below pins both. -/

namespace L4YAML.Tests.Guards.ConclusionCensus

open Lean Elab Command

/-- The left-hand sides of every `_ ∨ True`, in traversal order. -/
partial def lefts : Expr → Array Expr → Array Expr
  | .app (.app (.const ``Or _) x) (.const ``True _), acc => lefts x (acc.push x)
  | .app f a, acc => lefts a (lefts f acc)
  | .lam _ t b _, acc => lefts b (lefts t acc)
  | .forallE _ t b _, acc => lefts b (lefts t acc)
  | .letE _ t v b _, acc => lefts b (lefts v (lefts t acc))
  | .mdata _ e, acc => lefts e acc
  | .proj _ _ e, acc => lefts e acc
  | _, acc => acc

/-- Every `α` of an `Or.inl`/`Or.inr` at `(α := α) (β := True)`, for one side.
    Both sides are read: see the blind spots above. -/
partial def sides (side : Name) : Expr → Array Expr → Array Expr
  | e@(.app (.app (.app (.const s _) a) (.const ``True _)) _), acc =>
      let rest := match e with
        | .app f x => sides side x (sides side f acc)
        | _ => acc
      if s == side then rest.push a else rest
  | .app f a, acc => sides side a (sides side f acc)
  | .lam _ t b _, acc => sides side b (sides side t acc)
  | .forallE _ t b _, acc => sides side b (sides side t acc)
  | .letE _ t v b _, acc => sides side b (sides side v (sides side t acc))
  | .mdata _ e, acc => sides side e acc
  | .proj _ _ e, acc => sides side e acc
  | _, acc => acc

/-- Head constants in order — an instantiation-insensitive key, because the
    type's telescope and the value's terms carry different bound variables. -/
partial def skel : Expr → Array Name → Array Name
  | .const n _, acc => acc.push n
  | .app f a, acc => skel a (skel f acc)
  | .lam _ t b _, acc => skel b (skel t acc)
  | .forallE _ t b _, acc => skel b (skel t acc)
  | .letE _ t v b _, acc => skel b (skel v (skel t acc))
  | .mdata _ e, acc => skel e acc
  | .proj _ _ e, acc => skel e acc
  | _, acc => acc

partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | e => e

def ns : Name := `L4YAML.Proofs.StreamAccum

/-- One row per lemma: `name inl=a,inr=b …`, one field per conclusion
    conjunct, in the conclusion's own order.  Structure PROJECTIONS are
    excluded — they carry no proof term, so every conjunct of a projection
    would read as unpaid. -/
def census : CommandElabM (Array String) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? (ns ++ `flowKeyRoute_of_root)
  let mut rows : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if (env.getProjectionFnInfo? nm).isSome then continue
    let cs := lefts (conclusion ci.type) #[]
    if cs.isEmpty then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let ps := (sides ``Or.inr v #[]).map (fun e => skel e #[])
    let qs := (sides ``Or.inl v #[]).map (fun e => skel e #[])
    let mut out := s!"{nm.getString!}"
    for c in cs do
      let k := skel c #[]
      out := out ++ s!" inl={(qs.filter (· == k)).size},inr={(ps.filter (· == k)).size}"
    rows := rows.push out
  return rows.qsort

/-- The pinned census.  A conjunct that gains or loses a paying arm moves a
    row here; item 201 moved `flowKeyRoute_of_root`'s third and fifth from
    `inl=0` to `inl=1`. -/
def expected : List String :=
  ["back_col inl=0,inr=0",
   "close_col_of_base inl=0,inr=0",
   "dedent_cover_of_landing inl=1,inr=3",
   "explFrameValueLine inl=1,inr=1",
   "flowKeyHead inl=0,inr=0",
   "flowKeyRoute_of_open inl=2,inr=4 inl=0,inr=0 inl=0,inr=1 inl=0,inr=1 inl=0,inr=1",
   "flowKeyRoute_of_root inl=2,inr=2 inl=0,inr=0 inl=1,inr=2 inl=5,inr=0 inl=1,inr=2",
   "flowOpen_floor_at_prep inl=1,inr=1",
   "flowOpen_stamp inl=1,inr=2",
   "flowVPack_of_close inl=1,inr=1",
   "frameChainUnion inl=2,inr=0",
   "keyctx_of_preprocess inl=2,inr=3",
   "markerctx_of_landing inl=1,inr=3",
   "nodocctx_of_preprocess inl=2,inr=3",
   "scanValue_ok_park_facts inl=0,inr=0",
   "suffixctx_of_landing inl=1,inr=3"]

run_cmd do
  let got ← census
  if got.toList != expected then
    throwError "the conclusion census moved.\nexpected ({expected.length}):\n{
      String.intercalate "\n" expected}\ngot ({got.size}):\n{
      String.intercalate "\n" got.toList}"

end L4YAML.Tests.Guards.ConclusionCensus
