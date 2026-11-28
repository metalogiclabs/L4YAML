# Explicit-colon ownership and continuation composition

**WARRANTED, bounded:** Lean 4.36.0 checks the composition of successful
block-colon ownership with an incoming whole-entry continuation. It constructs
both the outgoing wide `SlotValues` and the framed `NodeValues`, retaining
all surviving smaller marks and the consumed mapping's arbitrary sibling tail.

An initialized concrete proof starts from the root question, constructs the
inner compact question, uses the actual successful `scanValue` on that source,
consumes a non-nil inner sibling tail, and then consumes the surviving root's
value to EOF. There is no free enclosing-route premise or assumed scanner
soundness in that concrete proof.

**UNKNOWN, production migration:** the actual explicit-colon producer checks
under its new mandatory incoming entry-step parameter. Its three real callers
still owe that parameter. This is a conditional producer result, not a funded
end-to-end repair or a critical-position retirement.

Continuation parent: `801aa32c222fa8590c91dff70950027232e19ace`.
Ownership parent: `7f7357ad10be9ad3d04372422b32f2119004dd24`.
Compiler: Lean 4.36.0, `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
The production diagnostic starts at the continuation parent's exact six-patch
source; ownership is transported from its separate owner-1383fa62 lineage.
No exact-owner-tree qualification is claimed for this combined experiment.
Intended capstone chain: explicit colon -> accumulation ->
`scanLoop_grammar_prod` / `scan_content_gives_stream_v2` (Blueprint 7.3 / 7.2).

## The decisive comparison

First, ownership was integrated while preserving the positive `NodeValues`,
the wide `EntryValues`, and the negative `NotQuestionPark AND TopUnmarked`
face. After resolving interface conflicts, the compiler retained exactly the
same 22 continuation labels, with zero additional errors. In particular,
own-column exclusion alone did not discharge either explicit-colon label.

Then `colon_payload_of_step` was composed at the actual
`colon_open_map_explicit`. The scanner's successful dispatch supplies
backward marked membership and output soundness; its ownership proof and
existing stack bounds establish that survivors are strictly below the owner.
The incoming entry step supplies their grammar continuation. The producer
stores both resulting contexts in its existing informative fields.

| Compiler comparison | Ownership-only integration | Composed producer |
| --- | ---: | ---: |
| Labelled demands | 22 | 23 |
| Additional interface/type errors | 0 | 0 |
| Explicit-colon outgoing-domain demands | 2 | 0 |
| Newly exposed incoming entry-step suppliers | 0 | 3 |

The removed labels are `R2_SLOT_EXPLICIT_COLON_DOMAIN` and
`R2_NODE_EXPLICIT_COLON_ANCESTORS`. The new mandatory labels are:

| Label | Actual caller |
| --- | --- |
| `R2_COLON_ENTRY_SUPPLIER_CLOSE` | `accum_block_on_closeThenBlock` |
| `R2_COLON_ENTRY_SUPPLIER_SEQUENCE_CONTENT` | `accum_block_on_pendingBlockContent` |
| `R2_COLON_ENTRY_SUPPLIER_SEQUENCE_PENDING` | `accum_block_on_pendingBlock` |

All other 20 labels are preserved, including
`R2_SLOT_PENDING_BLOCK_SUPPLIER`. The 22-to-23 comparison measures a changed
contract, not proof-debt payment. The incoming family was not available from
the callers' existing stream-returning route types. The soundness argument
is funded at all three actual callers; the entry-step arguments remain open.
No optional alternative, fresh decline or True escape was added.

## Initialized and independently audited witness

```yaml
? ? a
  : b
  ? c
  : d
: e
```

The incoming question state has marks `[0,2]`. The successful block-colon
output has marks `[0]`, offset 9 and column 3. Its `Sound` and stack
monotonicity are kernel-checked on the actual initialized source. The frame
returned by the new composition is spent on a real `SCompactMapTail.cons`
before the ancestor's value line is consumed. The earlier whole-source
sibling proof is explicitly forbidden as a dependency.

| Audited root | Dependency constants | Missing references | Axioms |
| --- | ---: | ---: | --- |
| Actual scanner/colon payload | 6,746 | 0 | Standard three |
| Sibling then ancestor, to EOF | 6,765 | 0 | Standard three |

Both dependency walks require the new composition, the scanner ownership
lemma, the checked successful scan and soundness proof, initialized root
construction, and the compact question constructor. They exclude
`scannerDrop`, `implicitContinue`, `dropClose`, `sorryAx`, and prior whole-source
supplier/consumption proofs. All three generic composition helpers also have
only `propext`, `Classical.choice`, and `Quot.sound`.

Pre-proof controls cover empty/root/nested and omitted values, a question
negative control, surviving marks `[0]` and `[0,2,4]`, sibling acceptance,
and the inherited 108 input/fuel combinations including fuel 0/1/2. These
executable controls are separate from the universal generic and finite
initialized grammar proofs. The inherited BOM row is not new BOM coverage.

## Actual producer boundary

Environment checks assert that the actual explicit-colon body spends
`colon_payload_of_step`, scanner own-exclusion, `scanValue_sound`, and the
scanner's backward marked-domain proof. They assert its mandatory entry-step
and soundness parameters and absence of transitive `sorryAx`.

The actual colon producer's raw five-axiom profile is byte-identical to the
accepted baseline: three standard axioms plus the same two inherited native
character/indicator facts. The compact producer's raw seven-axiom profile and
value-completion producer's raw 48-axiom profile are also byte-identical to
their accepted baselines. No complete failed module or capstone is promoted
from those local checks.

Full diagnostic source SHA256:
`cba9c99227e6c67853e79e4b3ecea1b4874e0ad1795e78508bbd50ecdaac78e2`.
Ownership-only source SHA256:
`4053579edac75eae347ddeb36b103f6e4a98f7e6eb5e4d0c7b2e146fc3867dba`.

## Residual and reuse

The generic composition and initialized sibling/ancestor proof are
**REUSABLE**. The production migration remains **CANDIDATE** and full
invariant closure **UNKNOWN**. All seven critical positions remain
unretired; the accepted 252/7/178/67 roster was not remeasured on a failed
variant.

Next useful experiment: retain the whole lower-entry family through the
actual `h_vpack`/sequence-slot suppliers, rather than projecting to a plain
stream route before calling the explicit-colon producer. Start with one
actual caller and assert that its exact supplier label disappears without
adding another free premise. Preserve the non-nil sibling quantifier.

The parallel canonical source audit of the pending-block supplier exposes
the same representation issue: a tail-parametric stream closure or a
nil-specialized selected-ancestor route does not carry the whole future
family. That is complementary evidence and a reusable design candidate;
this experiment does not claim to have repaired that separate supplier.

## Reproduction and negative lineage

Compile `Research/R2ValueOwnership/Controls.lean`, the new `Controls.lean`,
`ColonValues.lean`, and `Concrete.lean` against the parent's pinned imports,
using `lake env lean -o` with matching output paths under
`.lake/build/lib/lean`. Run `DependencyAudit.lean` and `AxiomBaseline.lean`.

For the deliberately failing production diagnostic, use a disposable exact
`9f1f7bc6` checkout, copy the research files, and apply the eight patches in
`reconstruction.json`. All eight intermediate source hashes were independently
restored. Run `lake env lean L4YAML/Proofs/Production/StreamAccum.lean` without
an output file: expect exit 1, exactly the 23 labels in
`diagnostic-errors.json`, no additional errors, and all producer audits.

Eight development sources restore exactly through compressed reverse patches.
Failed integration, namespace, option-interface and concrete-proof attempts
remain available in `lineage/` and `logs/`. Identical duplicate compiler logs
are represented by aliases in the reconstruction record. Editing failures
are not treated as contract refutations.

Only research evidence is published. The accepted production source is
restored unchanged. No production ref, runtime, guard, ceiling, hosted
workflow, native sweep, owner approval, merge or maintainer message was
changed or initiated. #384 recovery and publication were not repeated.
