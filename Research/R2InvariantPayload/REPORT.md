# Stored continuation consumed by the actual value-completion proof

**WARRANTED, bounded:** the experimental `PendingNode.pendingMapValue`
constructor now stores the consumption-closed context in both existing
informative fields, `h_expl` and `h_kslot`. The actual
`accum_content_on_pendingMapValue_indented` proof reads those fields, including
their open mapping tail. Its real caller forwards the existing scanner top
bound, which pays the frame cover. The previous external `h_entries` premise
and its catch-all caller demand are absent.

**UNKNOWN, full invariant:** the complete diagnostic exits 1 with 21 explicit
demands: 13 retained continuation demands and eight constructor demands, with
zero additional type errors. This is a changed contract, not a measurement
of proof debts paid. No critical position has been retired. The accepted
production source remains unchanged.

Parent `352304ba765995356d9b8e3e701fd09285e80e3e`; Lean 4.36.0, compiler commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. Published files are isolated
research evidence. The #384/item 541 qualification and documentation recovery
remain a separate lane.

## What the stored context preserves

`NodeValues sc start own slot` returns the whole `EntryValues` family after
an actual `SBlockNode (own + 1) .blockIn` completes. If the owner's mark has
already been consumed, it also retains `KeyFrames` at `[map own]` over that
family. This leaves the consumed mapping open for siblings before continuing
through a surviving ancestor. Its columns come from the real scanner
projection; no extra mark list or snapshot is stored.

The diagnostic conjoins this context with each existing informative payload;
it adds no optional alternative. A question with only its own column marked
is supplied from its actual `?` literal and full entry/tail route. A value
with no remaining marks is supplied from its existing node/tail route.
Non-singleton or nonempty marked domains remain explicit constructor demands.
The `ANCESTORS` label names those scopes; it does not establish reachability
or impossibility for every diagnostic state.

`NodeValues.framed_ancestor` spends the stored arbitrary sibling tail before
projecting the ancestor's explicit value continuation. `own_frame_cover`
proves the matching cover from stack monotonicity and the already stored
`currentIndent ≤ own` bound. The new frame is supplied with an informative
cover. Existing informative frames are preserved; this new construction is
used only where the old frame field declined. Other branches retain their
prior alternative. No new True cover escape was introduced.

The three content arms consume the stored context: one-line flow content
(including plain scalars), block scalars and multiline content. Two other
legacy flow/block interfaces still project the stronger payload down to their
old types. Full transport through those paths is not established.

## Concrete proofs and independent dependency checks

The standalone proofs construct the actual source prefix and entry route;
they do not assume a free root route. Scanner projections use kernel
`decide`, while public parser acceptance is checked separately by executable
guards. The question case supplies an explicit plain-key node witness, so a
conditional statement with an uninhabited node domain cannot stand in for
this check.

| Proof | Actual obligation exercised | Dependency constants |
| --- | --- | ---: |
| `actual_question_context` | Initialized `? a` question and an actual node | 6,134 |
| `actual_sibling_tail_consumed` | Consumed root value followed by a non-nil `? c : d` sibling tail, to EOF | 6,164 |
| `actual_ancestor_frame` | Initialized column-6 value, surviving marks `[0,2,4]`, actual `b` node, ancestor-0 frame | 6,163 |
| `actual_ancestor_frame_cover` | Actual column-6 scanner stack and its paid mapping-frame cover | 5,813 |

All four independent walks have zero missing references, exclude
`scannerDrop`, `implicitContinue`, `dropClose` and `sorryAx`, and permit only
`propext`, `Classical.choice`, `Quot.sound`. The first three require actual
`single`, `explicit` and `explicitEmpty` grammar constructors. Additional
guards require the actual question node, non-nil sibling constructor and
stored ancestor-frame reader. The cover check instead requires the actual
stack-monotonicity proof and `own_frame_cover`.

The finite sibling and ancestor proofs exercise separate sources. An
executable combined sibling/ancestor input is also accepted; a full formal
combined-source route is not claimed here. These are bounded source-grounded
results, not universal scanner/grammar correspondence or trace uniqueness.

## Actual producer boundary and remaining price

An environment audit checks the real constructor's two strengthened fields,
direct references from the actual producer body to both new frame readers,
absence of the old external premise, presence of the scanner-top parameter,
and connection of the actual caller to that producer. Inspection of the
checked caller expression confirms that its existing pending-value top fact
is the argument supplied. The accepted-source negative control confirms
that the new stored fields and readers are absent there.

The actual producer's raw `Lean.collectAxioms` output is byte-identical to
the parent baseline: 48 axioms, including the unchanged inherited
native-decide leaves, SHA256
`2ff7fe79deaca52cf869907334227bbd85475a8a64a3a96bbae2cc78b85da46a`.
It contains no `sorryAx`. The surrounding failed variant contains intentional
labelled failures and is not an accepted production module or capstone.

| Changed-contract boundary | Demands |
| --- | ---: |
| Retained close, other block, property, empty-value and union continuations | 13 |
| Question, compact-question, explicit-colon and keyless-colon domains | 4 |
| Implicit-colon and property-colon domains with remaining marks | 2 |
| Those two colon producers when their existing full-tail route declines | 2 |
| Additional type/interface errors in final diagnostic | 0 |

The parent's single `R2_VALUE_COMPLETION_ENTRY_VALUES` demand has been
replaced by obligations at actual context births. The count 14 → 21 is not
a comparable proof score. The older 22-demand lineage is retained too.
The last accepted roster remains 252 optional / seven critical ON; it was
not remeasured on this failed variant.

## Residual, next experiment and preserved lineage

The standalone context constructors, frame adapter, paid-cover lemma and
concrete regressions are **REUSABLE** within their checked boundaries. The
global storage/transport migration remains **CANDIDATE**, with universal
supply **UNKNOWN**.

Next: fund one actual question/colon producer with nonempty surviving marks.
Its existing wider `SBlockIndented` value-slot face is distinct from the new
`SBlockNode` domain; an adapter cannot assume the narrower domain covers every
caller. Price that one interface and retain the full entry/tail continuation
from its producer before extending more relays. The concrete ancestor payload
provides a positive regression, not the missing universal supplier.

The convergence with upstream remains a testable design hypothesis:
continuation evidence must retain both future value consumption and the
current mapping's siblings. Scanner membership and single-value continuations
alone have not discharged this stronger obligation. This experiment does not
prove those weaker contracts impossible.

Early misplaced-header errors, the metadata variable-shadow error, the
concrete stack-decide error and their corrected outcomes are retained. A
profiling attempt in the accepted checkout was interrupted after import and
has no result. An unguarded metadata debug print is explicitly excluded from
migration evidence; the final audits assert their observations. Four earlier
diagnostic sources reconstruct exactly from the final source using archived
reverse patches. Small development failures are preserved in a compressed log.

## Reproduction

Use the pinned manifest and matching built production imports. Build the
parent's `EntryValues` and `ConcreteSuppliers` research imports first, then:

```sh
mkdir -p .lake/build/lib/lean/Research/R2InvariantPayload
lake env lean -o .lake/build/lib/lean/Research/R2InvariantPayload/NodeValues.olean Research/R2InvariantPayload/NodeValues.lean
lake env lean -o .lake/build/lib/lean/Research/R2InvariantPayload/SourceControls.olean Research/R2InvariantPayload/SourceControls.lean
lake env lean -o .lake/build/lib/lean/Research/R2InvariantPayload/ConcretePayloads.olean Research/R2InvariantPayload/ConcretePayloads.lean
lake env lean Research/R2InvariantPayload/PayloadAudit.lean
lake env lean Research/R2InvariantPayload/StoredAuditPrecheck.lean
```

For the production diagnostic, use a disposable exact `9f1f7bc6` checkout and
apply the five patches listed in `reconstruction.json` sequentially. Their
independent restoration matches source SHA256
`34a785b2d813c429a948fd6cab467f10c92a63dbdb37a3e38d6fab07cb9d3345`.
Run `lake env lean L4YAML/Proofs/Production/StreamAccum.lean` without an output
file. Expected exit 1, exactly the 21 labels in `invariant-result.json`, the
stored-context audit and the baseline-identical producer profile. Do not
replace the accepted StreamAccum object with this intentionally failed source.

`RECEIPT.json` records every evidence-file hash. No runtime, production ref,
guard, ceiling, approval, merge or maintainer message was changed or attempted.
No hosted workflow or unchanged native qualification was launched.
