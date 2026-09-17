import L4YAML.Proofs.Production.StreamAccum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The `[210]` narrowing's consumer surface, pinned (DOCS item 183)

Row 19's 1c ends by narrowing `[211] l-yaml-stream`'s implicit-continuation
slot from `GOpt SLAnyDocument` to `GOpt SLExplicitDocument`.  The narrowing
instrument — flip the constructor, build — reports FIVE errors, at
`topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`, `bareNodeRoute` and
`structural_dispatch_to_pending`, and has reported those same five since item
166.  That number does not move when a payment lands, because the five are the
flip's WORK: the four raw routes it deletes and the one `SLAnyDocument.explicit`
wrapper it unwraps.  What a payment moves is the surface BELOW them — who still
reaches a raw route — and this file pins that.

**What is counted.**  Every non-internal constant of
`L4YAML/Proofs/Production/StreamAccum.lean` whose value applies one of the four
raw routes, or one of the five guards that stand in front of them
(`rootMapRoute_or_refused`, `rootMapRouteF_or_refused`, `bareNodeRoute_or_refused`,
`bareNodeRoute_or_refused_content`, `topLevelFlowResumeSep_or_refused`), with
its application count.  The guards themselves are excluded from their own
census — they are where the raw term is written, not where it is spent.

**The denominator is the module, not the environment.**  Other
`Tests/Guards/Proofs/` files apply the routes and the guards too, in worked
examples that document their interfaces (`StreamBlockLandingRefusal`,
`StreamMarkerLandingFace`); those are prose, not accumulation, and the module
filter is what keeps them out of the number.  A new consumer inside
`StreamAccum` — the direction that matters — fails this gate.

**Why the guards and not the raw routes alone.**
`Scratch/CensusRawRoutes.lean` counts the four raw terms and skips the guards,
which is what says each raw term is written once; it reads TWO holders and has
since item 181.  It cannot see a payment that removes a guard application,
which is every payment row 19 has left.  So this census counts both, and the
number it pins is the one future items have to move.

**And the escape the flip runs into.**  `block_dispatch_deferred` is
`PendingNode.pendingFlow`'s only producer, and `pendingFlow` is the one park
that offers the landing faces NO arm to take: its `CompletedTail` is FALSE by
construction (the token behind it is a `-`/`?`/`:`), it carries no suffix run,
no marker route, no document-prefix witness and no resume frames.  Every door
that reaches a raw route reaches it through that park among others, so the
deferral's own census is pinned here beside the flip's — R3's deletion is what
empties these arms, and the two numbers move together.

**By CLASS, since item 184; by ROUTE, since item 185.**  The deferral's
applications are partitioned in the source by the branch that reaches them.
Item 184 read three classes — the undecided stamp source (**9**), the mid-line
inline residue (**2**), and `pendingFlow`'s own arm (**1**).  Item 185 measured
the nine and found them three QUESTIONS with three different prices: the park's
pack stands off the landing's column (**3**), the park carries no pack at all
(**4**), or the fill is COMPACT and the stamp is the only thing that funds it
(**2**).  So the DEFERRAL lane counts five names rather than one and a class
emptying shows as a wrapper leaving the list.  The PACK PUNT lane beside it
counts what empties the inline class: `KeyPackPunt`'s two surviving reasons.
Both partitions and the input families they serve are documented at
[`BlockDeferralClasses`](BlockDeferralClasses.lean).

**Item 186 took the first site out, and a whole ROW with it.**  Twelve
applications across five consumer lemmas are now **ELEVEN across FOUR**:
`accum_block_on_noPending` reached the escape once, on the undecided stamp
source, and `noPending`'s new `h_noek` — a virgin block-context park is the
stream's seed, so its explicit-key register is dead — decides that source
instead of splitting on it.  A row leaving this census is what a class
emptying looks like, which is the shape item 184 built the lane for. -/

namespace L4YAML.Tests.Guards.FlipConsumerSurface

open Lean Elab Command

/-- Occurrences of each of `tgts` in an elaborated term, accumulated
    positionally.  ONE traversal for every target: these values are whole
    accumulation proofs and a traversal per name costs minutes. -/
partial def tally (tgts : Array Name) : Expr → Array Nat → Array Nat
  | .const n _, acc =>
      match tgts.findIdx? (· == n) with
      | some i => acc.set! i (acc[i]! + 1)
      | none => acc
  | .app f a, acc => tally tgts a (tally tgts f acc)
  | .lam _ t b _, acc => tally tgts b (tally tgts t acc)
  | .forallE _ t b _, acc => tally tgts b (tally tgts t acc)
  | .letE _ t v b _, acc => tally tgts b (tally tgts v (tally tgts t acc))
  | .mdata _ e, acc => tally tgts e acc
  | .proj _ _ e, acc => tally tgts e acc
  | _, acc => acc

def ns : Name := `L4YAML.Proofs.StreamAccum

/-- The four terms that hand `[211]`'s implicit continuation a BARE document —
    the ones the flip deletes. -/
def raws : List Name :=
  [`rootMapRoute, `rootMapRouteF, `bareNodeRoute, `topLevelFlowResumeSep]

/-- The five guards that stand in front of them, each with §9.2's landing
    refusal (and, at the content landing, its dangling reading) taken out of
    the raw route's domain. -/
def guards : List Name :=
  [`rootMapRoute_or_refused, `rootMapRouteF_or_refused,
   `bareNodeRoute_or_refused, `bareNodeRoute_or_refused_content,
   `topLevelFlowResumeSep_or_refused]

/-- `pendingFlow`'s only producer, and the four wrappers that partition its
    applications by the branch that reaches them (items 184–185): the stamp
    source's three ROUTES — the pack off the landing's column, no pack at all,
    and the compact fill — the mid-line inline residue, and, through the bare
    name, `pendingFlow`'s own arm, which the escape produces and which goes
    with the constructor.  The counts here are the DOMAIN's classes, so a class
    emptying shows as a wrapper leaving the list rather than as a total
    drifting. -/
def deferral : List Name :=
  [`block_dispatch_deferred,
   `block_dispatch_deferred_stamp_offcol,
   `block_dispatch_deferred_stamp_nopack,
   `block_dispatch_deferred_stamp_compact,
   `block_dispatch_deferred_inline]

/-- What empties the inline-residue class: the implicit-key pack's two
    surviving punt reasons (item 102 — the mid-line `:` composes whenever
    `colon_fires_implicit_key` gets a pack, so the residue IS the punt).  The
    other two reasons are refuted at their consumers and have no producer
    left.  `keyPackPunt_transport` is skipped for the same reason the wrappers
    are: it re-WRITES a reason it was handed rather than spending one. -/
def packPunt : List Name :=
  [`KeyPackPunt.dedent, `KeyPackPunt.noKeyContext]

/-- One census: the targets counted, and the definitions where the term is
    WRITTEN rather than spent, excluded. -/
structure Lane where
  tag : String
  targets : List Name
  skip : List Name
  deriving Inhabited

/-- `name: target=count …` for every StreamAccum constant that applies one of
    each lane's targets, sorted.  All lanes share ONE walk of the environment —
    the module's values are large and a walk per lane costs minutes.
    `allowOpaque := true` is required or every theorem reads as valueless and
    the census silently returns nothing. -/
def surface (lanes : Array Lane) : CommandElabM (Array (Array String)) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? (ns ++ `bareNodeRoute)
  -- every lane's targets, once, so one walk serves all of them
  let names : Array Name := lanes.flatMap (fun l => l.targets.toArray)
  let quals : Array Name := names.map (ns ++ ·)
  let zero : Array Nat := names.map (fun _ => 0)
  let mut rows : Array (Array String) := lanes.map (fun _ => #[])
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if env.getModuleIdxFor? n != modIdx then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let counts := tally quals v zero
    let mut base := 0
    for i in [0:lanes.size] do
      let lane := lanes[i]!
      let mut out := ""
      if !lane.skip.contains n then
        for j in [0:lane.targets.length] do
          let c := counts[base + j]!
          if c > 0 then out := out ++ s!" {lane.targets[j]!}={c}"
      base := base + lane.targets.length
      if out != "" then rows := rows.set! i (rows[i]!.push s!"{n.getString!}:{out}")
  return rows.map (·.qsort)

/-- The gate: each census must be its pinned list, row for row. -/
def pin (lanes : Array (Lane × List String)) : CommandElabM Unit := do
  let got ← surface (lanes.map Prod.fst)
  for i in [0:lanes.size] do
    let (lane, expected) := lanes[i]!
    if got[i]!.toList != expected then
      throwError "{lane.tag} moved.\nexpected ({expected.length}):\n{
        String.intercalate "\n" expected}\ngot ({got[i]!.size}):\n{
        String.intercalate "\n" got[i]!.toList}"

/-! ## §1  The raw routes' direct holders

ONE definition, ONE application.  Item 181 deleted the two crossed-window
payments and took this from three holders to two; item 182's runtime floor left
it untouched, because that item's kit lands below every one of these.  The
survivor is the INDENTED content landing, whose three callers park on
`pendingBlock`, `pendingMapValue` and `pendingProps` — item 156 measured that
none of the three is refutable (`danglingNodePos?` reads `none` at all of them
and all three inputs parse), so what is missing there is a ROUTE, the enclosing
park's own, and not a guard. -/

/-! ## §2  The guards' holders — the surface a payment moves

SEVEN definitions, FOURTEEN applications, one row per door:

| door | guard(s) | what still reaches the raw arm |
|---|---|---|
| `accum_block_on_closeThenBlock` | `bareNodeRoute_or_refused` | the `-` lane's on-level landing — a `[183]` already open at this column (`- - a⏎- b`, `a:⏎- x⏎- y`, item 166): a missing ROUTE, the open sequence's continuation |
| `accum_content_pending` ×2 | `bareNodeRoute_or_refused_content` | `pendingFlow`'s break-crossed landings ALONE (item 174) — both `h_op` halves refute for a park with a completed tail |
| `accum_flow_open_depth0` | `topLevelFlowResumeSep_or_refused` | the two content parks at `h_op = true`, whose inputs the scanner REFUSES (§7 of `StreamFlipRemainderMap`), plus `pendingFlow` |
| `colon_open_map`, `question_open_map` | `rootMapRoute(F)_or_refused` | the sibling `:`/`?` landing whose park pays no resume face (item 173's cascade covers the rest) |
| `content_dispatch_routed` ×2 | `rootMapRoute(F)_or_refused` | the same, at the content landing's key side |
| `flowKeyRoute_of_root` | `rootMapRoute(F)_or_refused` | the sibling flow key whose park pays no frame (item 176's cascade covers the rest) |

Each `rootMapRoute_or_refused` row is paired with its entries-level twin
`rootMapRouteF_or_refused`, which is why those counts come in twos. -/

/-! ## §3  The deferral beside it

FOUR definitions, ELEVEN applications (item 186 — five and twelve before it).
`pendingFlow` is not a `[210]`
construction site and never appears in the flip's five errors — it is the park
whose arms have nothing to pay the landing faces WITH, so it keeps the guards'
fallback arms alive wherever it can reach them.  Pinning it here is what makes
that dependency checkable rather than remembered: R3's deletion empties arms
this census counts, and a change to either number should be read against the
other.

The rows below are the DOMAIN's shape, not the module's: each landed-`:`
consumer contributes one `offcol` and one `nopack` because its `by_cases` on
the park's pack has exactly those two stuck arms, and the two consumers with a
compact-fill arm contribute a `compact` each.  The asymmetric row was
`accum_block_on_noPending`'s, and item 186 removed it: that park carries no
pack because it carries nothing at all, and the register face it does carry
now says the class-A branch cannot reach it. -/

/-! ## The gate

All three lanes, in one walk of the module. -/

#eval show CommandElabM Unit from
  pin #[
    ⟨⟨"RAW ROUTES", raws, raws.map (ns ++ ·) ++ guards.map (ns ++ ·)⟩,
      ["content_dispatch_after_close: bareNodeRoute=1"]⟩,
    ⟨⟨"GUARDS", guards, guards.map (ns ++ ·)⟩,
      ["accum_block_on_closeThenBlock: bareNodeRoute_or_refused=1",
       "accum_content_pending: bareNodeRoute_or_refused_content=2",
       "accum_flow_open_depth0: topLevelFlowResumeSep_or_refused=1",
       "colon_open_map: rootMapRoute_or_refused=1 rootMapRouteF_or_refused=1",
       "content_dispatch_routed: rootMapRoute_or_refused=2 rootMapRouteF_or_refused=2",
       "flowKeyRoute_of_root: rootMapRoute_or_refused=1 rootMapRouteF_or_refused=1",
       "question_open_map: rootMapRoute_or_refused=1 rootMapRouteF_or_refused=1"]⟩,
    ⟨⟨"DEFERRAL", deferral, deferral.map (ns ++ ·)⟩,
      ["accum_block_on_closeThenBlock: block_dispatch_deferred_stamp_offcol=1 block_dispatch_deferred_stamp_nopack=1 block_dispatch_deferred_stamp_compact=1 block_dispatch_deferred_inline=1",
       "accum_block_on_pendingBlock: block_dispatch_deferred_stamp_offcol=1 block_dispatch_deferred_stamp_nopack=1 block_dispatch_deferred_stamp_compact=1",
       "accum_block_on_pendingBlockContent: block_dispatch_deferred_stamp_offcol=1 block_dispatch_deferred_stamp_nopack=1 block_dispatch_deferred_inline=1",
       "accum_content_pending: block_dispatch_deferred=1"]⟩,
    ⟨⟨"PACK PUNT", packPunt,
       [ns ++ `keyPackPunt_transport,
        -- the type's own generated eliminators, which mention every
        -- constructor by construction and spend none
        ns ++ `KeyPackPunt.casesOn, ns ++ `KeyPackPunt.recOn]⟩,
      ["accum_flow_open_depth0: KeyPackPunt.dedent=1 KeyPackPunt.noKeyContext=1",
       "colon_fires_implicit_key: KeyPackPunt.dedent=1 KeyPackPunt.noKeyContext=1",
       "colon_fires_props_key: KeyPackPunt.dedent=1 KeyPackPunt.noKeyContext=1",
       "content_dispatch_routed: KeyPackPunt.noKeyContext=2",
       "entryKeyPack_of_dispatch: KeyPackPunt.dedent=2",
       "entryPropsKeyPack_of_dispatch: KeyPackPunt.dedent=2",
       "flowKeyPack_of_close: KeyPackPunt.noKeyContext=1"]⟩]

end L4YAML.Tests.Guards.FlipConsumerSurface
