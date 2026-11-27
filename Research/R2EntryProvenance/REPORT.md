# R2: three relays compile, but actual entry ownership still blocks the consumers

**WARRANTED within the local Lean 4.36.0 boundary.** The sibling, nested-block
and compact-sequence pair relays all compile in the actual producer. The
selected helper, accumulation and capstone axiom reports are byte-identical
to baseline. Requiring the informative continuation at the two real colon
callers still fails at exactly the four previously identified residuals.

| Experiment | Result | Boundary |
| --- | --- | --- |
| Exact source baseline | 239 build jobs, exit 0 | StreamAccum target |
| Three omitted relay repairs | 239 build jobs, exit 0 | Conditional pair transport; unchanged existential owner |
| Axiom comparison | Three profiles byte-identical | Helper, accumulation, scan_content_gives_stream_v2 |
| Both mandatory colon consumers after relay repairs | Exit 1; same four labelled errors | No accepted universal supplier or critical retirement |
| Initialized native source controls | 14/14 parser-accepted; all assertions pass | Real scanner/parser, not proof-disjunct observation |

The four remaining compiler labels are `R2_SEED_OWNER_MISMATCH`,
`R2_SEED_UNAVAILABLE`, `R2_SEQ_OWNER_MISMATCH`, `R2_SEQ_UNAVAILABLE`.
The complete failed build log and exact candidate patch are retained.
The three-relay implementation is **REJECTED as sufficient to discharge the
mandatory consumers**, not refuted as a conditional transport construction.

## Decisive entry-order evidence

The owner witness is accepted:

```yaml
? ? a
  : - b
```

Its first explicit `:` lands at column 2, consumes that mark and leaves mark
0. It is scanner step 3; the first sequence indicator is step 4. Thus the
required ancestor continuation precedes all three sequence repark producers.
The three sequence relays cannot be the first source of that continuation
for this accepted source. This conclusion concerns route order; it does not
claim to observe an optional proof field at runtime.

A new accepted control rejects a tempting ownership shortcut:

```yaml
? ? ? a
  : - b
: c
```

| First value landing | Questions encountered | Marks before preprocess | Marks after preprocess | Value column | Marks after value | Earlier sequence indicators |
| --- | --- | --- | --- | --- | --- | --- |
| Two-question witness | 0, 2 | 0, 2 | 0, 2 | 2 | 0 | 0 |
| Skipped inner question | 0, 2, 4 | 0, 2, 4 | 0, 2 | 2 | 0 | 0 |
| All three entries get values | 0, 2, 4 | 0, 2, 4 | 0, 2, 4 | 4 | 0, 2 | 0 |

"Latest question column equals the next value landing" is **REJECTED** by
the second row. This does not identify the owner chosen by an existential
proof witness. It establishes why equating an arbitrary owner with the
landing needs a real correspondence proof.

There are 12 explicit value steps with surviving ancestors in the 14-source
grid, six column-2 value steps before any sequence indicator, and two value
landings below the last question while an ancestor survives. Sibling, nested
and compact sequences are exercised both in keys and after explicit values;
implicit-colon, flow and root controls are included. The discriminator is
copied from `scanValue` and checked against the actual stamp behavior at
every counted explicit value.

## Highest-leverage residual

**CANDIDATE next experiment:** retain the actual entry-parametric
continuation at key completion and transport it through preprocessing to
the live entry selected by the explicit colon. Test the skipped-inner
question control before attempting a universal ownership invariant. Bind the
continuation to the actual question/key derivation, not just one existential
column or a generic empty-key constructor.

The source explains the distinction. `pendingMapValue.h_expl` can take a
full `SBlockMapEntry`; `explEntryChain_of_keyContent` projects its ancestor
route through `explicitEmpty`. The content producers expose a one-value
`h_vpack`, whereas the consuming R2 obligation needs the inner explicit
value followed by the surviving ancestor's value. This is a source-level
candidate for where richer evidence must be retained, not a proof that it
is the only possible repair. `RegisterWitness.QuestionEntry` supplies a
surface question and landing; it does not itself contain this grammar
continuation.

The experiment adds no new optional alternative to the prior R2 carrier
design. No capstone statement, scanner/runtime, census pin or production ref
is changed. The source checkout was restored clean to its exact original
StreamAccum blob. No new hosted workflow was launched.

No full-default, binding, documentation or candidate census qualification
is claimed. The established seven production critical positions remain an
open frontier; this experiment proves no retirement. Upstream PR #387
remains a separate source line, inspected at 9f1f7bc6; these patches were
tested on the pinned research source, not presented as an integration into
that PR.

## Reproduction and lineage

Use an unmodified checkout of commit
`12f27421d70b7e5039fc01ed946a19141156773e` with the pinned Lean 4.36.0 and
manifest dependencies. Keep this evidence directory in a separate checkout.

1. Build `L4YAML.Proofs.Production.StreamAccum`; run `AxiomAudit.lean` using
   that checkout's `lake env lean`, saving its output.
2. Apply `three-relays.patch` to the source checkout. Build the same target,
   rerun `AxiomAudit.lean`, and compare its output byte for byte.
3. Restore the original source. Apply `mandatory-consumer.patch` instead;
   build the same target. Expect exit 1 and the four labelled residuals.
4. Run `ReachableEntryProbe.lean` with `lake env lean --run` in the source
   checkout. It imports only unchanged scanner/parser dependencies. Expect
   the JSON summary in `entry-probe.jsonl`.
5. Restore the original StreamAccum file and check its Git blob is
   `7f731ef53f93aebc969b9790ad03bc14b7cd029e`.

`three-relays-only.patch` isolates the incremental change from the prior
19-edit transport source. `prior-19-edit-spec.json` retains its exact
anchors. `RECEIPT.json` binds all tested source hashes, exits and declared
verification limits. `SHA256SUMS` binds the retained evidence files.

Negative lineage is preserved: original actual-producer generator failure
45940594116; corrected four-residual diagnostic 45946458630; KeyFrames
generator failure 45961304424; KeyFrames semantic diagnostic 45961669654.
Two local probe development errors (record layout and unavailable
Option.flatten API) are retained separately; neither is a mathematical
refutation. The initial successful twelve-case run is retained alongside
the fourteen-case extension and its predictions.
