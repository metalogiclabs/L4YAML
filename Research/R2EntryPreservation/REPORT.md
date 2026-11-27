# Full-entry continuation composition: verified local result, open supplier

**WARRANTED within the local Lean 4.36.0 boundary.** Two result-parametric
grammar lemmas retain an actual explicit entry, its own value, and the
enclosing continuation. They compile at real production consumers and are
reached from `scan_content_gives_stream_v2`. This is not a universal invariant
for every reachable scanner state. All seven critical positions remain.

The source pin is upstream PR #387, commit
`9f1f7bc60cf54741c1bf5d0c0618ee680268ed15`, tree
`0c7dced413db0510b0a0a144ca2ca74111cf6a77`. The runtime is unchanged.

## What is new

`explicitEntryValueRoute` accepts the actual question literal and a route
over the whole `SBlockMapEntry`. Completing its key leaves its own explicit
value available. `compactEntryRoute` plugs the whole compact mapping,
including its sibling tail, into the caller's slot. Both are polymorphic in
the resulting predicate, so that predicate can itself await another value.
Neither lemma depends on any axiom.

The real `explEntryChain_of_keyContent`, `compactExplicitKeyFrame` and
`compact_open_map` consume the helpers. A formal composition check retains
three consecutive value lines and a separate check retains the compact
mapping's sibling tail. Wrong-question and wrong-index applications must fail
to elaborate. There is no new optional field, alternative or scanner datum.

The previously qualified compact `h_explUp` writer from run **45968133262**
is included using the same composition. Its literal and marked-domain cover
remain tied to the actual compact entry. That writer is retained prior work,
not a newly discovered payment or a universal ancestor supplier.

## Verification completed at this checkpoint

| Check | Observed result |
| --- | --- |
| Production `StreamAccum` and `DocumentProduction` | 241 jobs, exit 0 |
| Existing affected axiom profiles | Six profiles byte-identical to baseline |
| Both new lemmas | No axioms |
| Three-value, sibling-tail and identity composition checks | Exit 0 |
| Adversarial executable | 62,527 / 62,527 passed |
| Complete ordinary test command | Exit 0; 64,686 / 64,686 verified checks |
| New P145 controls | 60 initialized source rows, 165 checks |
| Native corpus matrix | 869 passed / 0 failed / 151 skipped |
| Event score | 347 / 358; eleven standing event differences |
| Same capstone instrument, before and after | Seven ON positions in both |
| Capstone-reached StreamAccum constants | 1152 / 1262 → 1154 / 1264 |

The P145 controls cover depths 2–6, omission of inner values, and scalar,
flow and sequence values. Forty-five checks explicitly reject the shortcut
that the most recently scanned question must own the next value. Native
scanner/parser controls cannot observe which Prop-valued proof arm was used.

The corpus was materialized from the project's pinned submodule commit
`478062b90533880678b1c9243891957c0f2a1b2b`. All 351 source blob hashes and the
complete `src` tree hash were independently recomputed; see `corpus-receipt.json`.

**Instrument reconciliation:** the standalone capstone tool reports
`pack-declines: on=0 off=0` on the clean baseline too. The prior compact-writer
artifact's zero reading therefore supplies no evidence of newly paid critical
declines. The seven-position roster is unchanged. No census pin is weakened.

## The stronger producer demand is still UNKNOWN

`key-completion-demand.patch` demands a pair of future value lines for every
ordered pair of actually marked entries at the real scalar-key producer,
`accum_content_on_pendingMapValue_indented`. The current-question branch with
its ancestor continuation elaborates through `explicitEntryValueRoute`.
Three remaining branches are deliberately exposed as labelled proof goals:

- `R2_KEY_CURRENT_ENTRY_NO_ANCESTOR_CONTEXT`
- `R2_KEY_OTHER_SURVIVING_ENTRY_CONTEXT`
- `R2_KEY_NONQUESTION_ENTRY_CONTEXT`

The diagnostic exits 1 at exactly these sites, with no additional immediate
type-error sites. It prices the unimplemented suppliers; the explicit `fail`
sites are not a refutation, proof of impossibility, or exhaustive proof search.
The failed diagnostic is not part of the production source.

The remaining architectural candidate is a family of actual entry contexts,
indexed by the scanner's surviving slots and their question positions.
Keeping the latest entry alone does not supply another entry surviving
preprocessing. The existing skipped-inner-question control remains decisive.

## Reconciled parallel work and the actual survivor contract

Parallel evidence at `686cea942c674dbcb984b66cf9cd4da4afd4fa92` independently
reproduces the same three key-ready residual classes and reconciles retention
run 45973926202. The local price above is an independent reproduction, not an
additional discovery or payment.

`StrictContractChecks.lean` is accepted by the pinned compiler. Its
`strictPairAt_landing` proves that a retained pair over strictly smaller marks
suffices for every actual post-landing mark. Output-stack monotonicity and the
top bound place each survivor at or left of the consumed column; consumption
rules out equality. Its axioms are exactly `propext`, `Classical.choice` and
`Quot.sound`.

This proves sufficiency of the smaller domain at the caller boundary. It does
not construct entry contexts, refute the older all-different-marks contract,
or establish the complete retention migration. The local migration supplies
existing output-stack monotonicity at all three colon calls. Its final compiler
run exits 1 at exactly 22 labelled proof demands and no additional type-error
sites. The actual `colon_open_map_explicit` declaration is elaborated; its
printed axiom profile contains the three standard axioms and two existing
native-decide axioms from `dispatchBlockValue_full_prod`, with no `sorryAx`.
The surrounding caller declarations remain unaccepted because of their
unimplemented demands. This is a diagnostic result, not a passed migration.

| Remaining explicit demand | Sites |
| --- | ---: |
| Key writers: surviving owner, absent chain, absent question | 9 |
| Other content/block callers | 2 |
| Retained fields at closes, properties, empty values and entry union | 11 |
| Additional type errors | 0 |

`retention-diagnostic.json` records every exact label and source line. The
prior migration's 26 sites included 15 unclassified interface errors. Exposing
missing fields as explicit demands changes that accounting; 26 to 22 is not a
measurement of proof debt paid. All seven critical positions remain. The
strict diagnostic source SHA256 is
`1a482089f93091d8d2daafbcdec875c2f64ade131e343ddfe8b11c37186dcbaa`.
Both sequential patches independently reconstruct those exact bytes.

A SIGKILL/resource attempt, a deliberate 2048 MiB memory-cap failure, and a
malformed union-field attempt are retained separately. The final run has no
artificial memory cap and finishes with the 22 explicit demands above. These
development/resource failures neither refute the contract nor qualify the
migration.

## Qualification and lineage limits

The full default build first exhausted disk space. That attempt was stopped
(exit 130) after preserving its resource errors. Generated executables were
relocated with byte-for-byte SHA256 checks; source and executable bytes were
not changed. The resumed full default build was stopped after the parallel
retention completion changed the integration priority. RelaySupplyCensus,
FreeSurfaceCensus and ConclusionRouteCensus compiled; this is not a passed full
default build. The complete ordinary test command subsequently passed after
building the fresh checkout's missing limit-test entry point. Its first
missing-entry-point failure is retained. Full repository qualification, fresh
hosted CI, bindings and documentation are not claimed here.

The initial P145 Nat/Int elaboration mistake and an unsupported interpreter
invocation are retained as development failures. They are not mathematical
refutations or failures of the subsequently successful native executable.

Prior lineage: 85f3188f's three-relay insufficiency result and skipped-owner
controls; compact writer 45968133262; question-producer diagnostic
45968167777. No production PR, upstream ref, workflow permission or approval
was changed. The copied worktree's shared Git metadata was isolated before
publication; its original checkout was restored to the same detached source.

## Reproduce the bounded result

Use this source branch with Lean 4.36.0 and its pinned manifest/submodule.

```sh
lake build L4YAML.Proofs.Production.DocumentProduction
lake env lean Research/R2EntryPreservation/CompositionChecks.lean
lake env lean Research/R2EntryPreservation/AxiomAudit.lean
lake env lean Research/R2EntryPreservation/StrictContractChecks.lean
lake build adversarialinstantiation tests demo limittests
lake exe adversarialinstantiation
lake run run-all-tests -- Research/R2EntryPreservation/suites
lake exe suiterunner
lake exe eventscore
```

`candidate.patch` binds the implementation and tests against the upstream pin.
Apply the separate diagnostic patch only in an expendable checkout; its
three labelled failures are expected and must never be promoted as a proof.


The retention diagnostic is a separate source variant, not the helper branch
above. Starting from the exact upstream pin, apply `retention-original.patch`
then `retention-strict-delta.patch` in an expendable checkout and invoke
`lake env lean -j 1 L4YAML/Proofs/Production/StreamAccum.lean`. These patches
must not be applied on top of `candidate.patch`. The deliberately labelled
`fail` goals are expected failures; a successful outer harness cannot qualify
this diagnostic as a completed migration.

The smallest useful next experiment is to provide one missing enclosing-entry
context at the actual colon transition, carry it through one real key writer,
and check its later ancestor landing. More conditional transport of an absent
context cannot construct that context. The strict survivor contract and the
whole-entry composition reduce the requirements this experiment must meet.
