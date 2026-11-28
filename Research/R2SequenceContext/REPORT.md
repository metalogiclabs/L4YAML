# Sequence tails retain the ancestor family at the pending-block boundary

**WARRANTED, bounded:** Lean 4.36.0 checks the sequence-context construction
and transport lemmas, plus two initialized source-to-EOF proofs: a sequence
opening a compact question and a sibling sequence entry followed by an
ancestor value. The latter spends a genuinely non-nil sequence tail.

**PRICED, incomplete migration:** the diagnostic stores the whole family in
the existing mandatory `PendingNode.pendingBlock.h_close_entry`. The actual
`accum_block_on_pendingBlock` reads it for its wide slot and its sibling,
nested and compact sequence constructions, without a new external context
premise. `R2_SLOT_PENDING_BLOCK_SUPPLIER` is absent. The complete module still
exits 1 at 23 labelled obligations, zero additional type errors. No critical
position has been retired.

Parent `801aa32c222fa8590c91dff70950027232e19ace`; compiler commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. Published changes are research
evidence only. Accepted production source SHA256
`f1eece1acca9f124666aa8fcc8fe5b591c316df35b292b32ed28af491a25772a`
remains unchanged. The explicit-colon ownership integration is a separate
active lane and was not edited or duplicated.

## The continuation and its actual writers

`SequenceValues sc start n slot` quantifies over the actual
`SBlockIndented n .blockIn` entry followed by an arbitrary `SCompactSeqTail n`.
It returns `EntryValues` over the real scanner's marked-column projection.
The existing mandatory field retains its old stream result and conjoins this
family; no optional carrier, fresh decline, mark list or snapshot is added.

Restriction across a real step uses backward marked membership. Sibling
transport conses the actual new entry and its tail onto the old continuation.
Nested transport uses the real block-sequence constructor; compact transport
uses `SBlockIndented.compactSeq`. The wide slot needed by `compact_open_map`
is the current sequence continuation read with a nil tail.

The initial prediction of **eight** construction sites is **REFUTED**. An
independent recursive walk of accepted Lean expressions finds seven:
1 + 2 + 1 + 3 in the four actual producer declarations. There is one
pending-entry sibling construction, not two. The direct source inventory
matches these seven edited sites.

| Actual construction class | Family supply in the diagnostic |
| --- | --- |
| Root sequence | Existing proved empty marked domain and actual root tail |
| Compact fill of a map-value slot | Stored wide `SlotValues` and actual compact sequence |
| Pending-entry sibling | Stored sequence family and actual non-nil tail cons |
| Nested sequence | Stored sequence family and actual nested collection |
| Compact sequence | Stored sequence family and actual compact collection |
| Landed sequence | Empty-domain case supplied; nonempty family missing |
| Completed-content sibling | Empty-domain case supplied; nonempty family missing |

The five constructed suppliers are checked under the strengthened contract;
they are not five independently retired capstone debts. The new obligations
are at the actual landed and completed-content births, rather than at the
downstream wide-slot reader.

## What the proofs do and do not preserve

The helpers preserve an arbitrary tail at the current sequence's width.
Nested and compact composition close an enclosing sequence with a nil tail.
They do not establish transport of every later enclosing-sequence sibling
through `h_seqF`. Completed-content carriers still use their old interface.
Neither limitation is hidden by an optional fallback.

The old pending-block pair obligation is now supplied when the consumed
owner was marked before the scan, using the stored family, actual completed
empty entry and backward marked membership. The remaining labelled branch
explicitly has that owner unmarked before the step. This is a narrowed
residual, not an impossibility proof. The complete pending-block declaration
still contains a retained labelled failure and is not claimed sorry-free.

## Initialized witnesses and independent dependency audits

Pre-proof controls cover root and empty entries, zero/nonzero ancestor
domains, siblings, nested and compact sequences, and multiple ancestors.
Kernel reductions check successful scanner observations and the relevant
marked projections. Public parser acceptance is a separate executable guard.

The first full grammar witness covers:

```yaml
? - ? a
    : b
: c
```

It constructs the initialized root slot, the sequence family at column 2,
the wide pending-block slot, and the compact question at column 4. Kernel
checks distinguish marks `[0]` after the dash, `[0,4]` after the question,
and `[0]` after the inner colon. The actual key and both values are consumed
to EOF without assuming an enclosing root route.

The second full witness covers:

```yaml
? - a
  - b
: c
```

It applies the same sibling transport lemma used in the production
diagnostic, consumes the second actual entry and then the root value. The
helper constructs `SCompactSeqTail.cons`; a nil-tail-only test cannot pass
the dependency guard.

| Independently audited complete proof | Dependency constants |
| --- | ---: |
| Sequence → compact question → inner/root values | 6,223 |
| Sequence sibling → ancestor value | 6,193 |

Both walks have zero missing references, require six actual grammar/context
constructors and two relevant readers, and allow only
`propext`, `Classical.choice`, `Quot.sound`. They exclude `scannerDrop`,
`implicitContinue`, `dropClose`, `sorryAx` and the earlier whole-source
supplier/consumption proofs. The four sequence transport helpers likewise
use only the standard three axioms. These are bounded initialized grammar
proofs, not universal scanner/grammar correspondence or trace uniqueness.

## Compiler boundary, residual and next experiment

An environment audit asserts that the actual mandatory field stores
`EntryValues`, that the actual pending-block body reads all four sequence
helpers, and that no separate external context parameter was added. The
accepted-source control verifies the old field lacks this family and checks
the seven-construction inventory.

The compact producer's raw seven-axiom profile remains byte-identical to
the parent, SHA256
`aa7c1dbfb75ca64c008974e967eb5baa72230b99356e770f929882dc526f10bb`.
The value-completion producer's 48-axiom profile also remains byte-equal,
SHA256 `2ff7fe79deaca52cf869907334227bbd85475a8a64a3a96bbae2cc78b85da46a`.
Those two profiles contain no `sorryAx`. This does not qualify the complete
pending-block declaration or the intentionally failed module.

| Final changed-contract obligations | Count |
| --- | ---: |
| Retained continuation obligations, including the narrowed pair residual | 13 |
| Other constructor obligations from the parent | 8 |
| `R2_SEQUENCE_LANDED_FAMILY` | 1 |
| `R2_SEQUENCE_COMPLETED_FAMILY` | 1 |
| Additional type/interface errors | 0 |

The change 22→23 is not a proof-debt score. The prior accepted
252 optional / seven critical ON / 178 OFF / 67 unresolved roster is retained
without remeasurement on this failed source. Universal supply and all seven
critical retirements remain **UNKNOWN**; the full migration is **CANDIDATE**.
The checked generic helpers and bounded regressions are **REUSABLE**.

Next: carry the same family through the actual content-completion interface
into `pendingBlockContent.h_closable_entry`. The current content caller
deliberately projects the old stream result for that legacy API; the
completed-content sibling consequently lacks the whole family. Price that
one interface before widening more relays. The landed-family obligation and
enclosing-sequence-tail transport remain separate.

The forward-declaration failure, namespace-scope failure reaching the
100-error limit, failed immediate-child inventory audit, and concrete
decidability correction are preserved. They are editing/instrument failures,
not mathematical refutations. A root-qualified helper declaration within the
original scope corrected the private-alias issue. Both failed production
sources reconstruct exactly from the final source.

## Reproduction

Use the pinned manifest and matching production/parent research imports.
Compile `Controls`, `SequenceValues`, `ConcreteContexts` in that order with
`lake env lean -o` into their matching
`.lake/build/lib/lean/Research/R2SequenceContext/*.olean` paths. Run
`lake env lean Research/R2SequenceContext/DependencyAudit.lean` and
`lake env lean Research/R2SequenceContext/BaselineAudit.lean`.

For the failed production diagnostic, use a disposable exact `9f1f7bc6`
checkout and apply the seven patches in `reconstruction.json`. Independent
restoration matches source SHA256
`02fd3926d541cf5d70c64798ce1bffbb3ea7b226aafa3d2c22539ffd002e9ca1`.
Run `lake env lean L4YAML/Proofs/Production/StreamAccum.lean` without an output
file. Expected exit 1, exactly the labels in `sequence-result.json` and all
three stored-context audit messages. Do not install this failed module's
output as an accepted production object.

`RECEIPT.json` records the evidence hashes. No runtime, production ref,
guard, ceiling, hosted workflow, native sweep, approval, merge or maintainer
message was changed or initiated.
