# Two actual explicit-colon callers obtain the stored continuation

Heath Sanchez · 28 November 2026

**WARRANTED within the checked boundary:** the pending-sequence and
completed-sequence colon call paths now supply the incoming entry continuation
from their existing mandatory fields. Neither caller gains an external
continuation parameter. Their elaborated external types are byte-identical
to the integrated baseline. Four specific compiler demands disappear, with
no replacement labels or additional type errors.

**UNKNOWN full migration:** the complete experimental module still exits 1
at 19 retained obligations. The general close caller and landed-family
supplier remain open. All seven critical positions remain unretired and
were not remeasured. This is research evidence, not a qualified production PR.

## The missing distinction

An ancestor-list cover says every actual mark is included in the list. It
does not say every listed column is still marked. The old selected-ancestor
path could therefore ask an already-consumed column to supply a pending
explicit entry's continuation.

The new `live_landing_of_no_stamp` proves, from the existing scanner
soundness and preprocessing facts, that the non-stamping colon source has
its owner marked in the actual before-state. Conversely, an unmarked
candidate cannot enter that source branch. No new scanner flag is introduced.

The actual callers now use the explicit-value route only with a marked
owner. On the stamping-source branch an unmarked candidate uses the
already-existing generic route. This is an explicit change in proof-route
selection; it is not claimed to have proved a new continuation for that
generic route. Its separately retained constructor obligations stay open.

For a live owner, `entry_step_at_landing` reads the caller's stored
`EntryValues`, extracts its whole owner step and restricts its lower domain
through actual preprocessing. The same stored family supplies the paired
ancestor line. Both omission/value alternatives and arbitrary consumed-map
tails are retained in the entry step.

## Actual production experiment

The baseline reconciles the continuation-contract result
`8d4596f26cf430df50d0e3f1e0dce2ea1104f83d` with the colon-composition result
`45db495873471857987ff1e0c71e826e991adc3a`. The former reuses the completed
sequence work at `d1a012df`; the latter reuses ownership at `7f7357ad`.
These parent results are not claimed as new discoveries.

| Actual caller | Existing source of the incoming family |
| --- | --- |
| `accum_block_on_pendingBlockContent` | Mandatory completed-entry field, through `h_completedContext` |
| `accum_block_on_pendingBlock` | Mandatory pending-entry field, through `h_sequenceContext` |

Both actual colon applications contain `entry_step_at_landing`. Environment
audits check the actual argument terms, require the scanner ownership and
pair readers, and reject direct or referenced transitive `sorryAx` in those
supplier terms. The containing dispatchers still have their unrelated
failures; neither whole dispatcher is declared proved.

| Fixed integrated interface | Baseline | Supplied callers | Old selection restored at one site |
| --- | ---: | ---: | ---: |
| Exact compiler labels | 23 | 19 | 20 |
| Additional errors | 0 | 0 | 0 |
| Actual caller external types preserved | — | 2/2 | 2/2 |

Removed labels:

- `R2_COLON_ENTRY_SUPPLIER_SEQUENCE_CONTENT`
- `R2_COLON_ENTRY_SUPPLIER_SEQUENCE_PENDING`
- `R2_OTHER_BLOCK_CONTENT_PAIR_UNMARKED`
- `R2_OTHER_PENDING_BLOCK_PAIR`

All other 19 labels are retained. The negative control restores the old
unmarked-candidate selection at one real completed-sequence call site. It
adds exactly `R2_OWNER_FROM_COVER_NEGATIVE_CONTROL`, exposing the owner fact
that coverage alone does not supply. It preserves the other 19 failures.
This tests the actual routing distinction, not impossibility of every
alternative proof from the old interface.

Direct references to `block_dispatch_deferred_stamp_offcol` fall from one
to zero in each caller, because that non-stamping/unmarked case is ruled out
by the scanner lemma. References to the other audited escape helpers do not
increase; `dropClose` remains absent from both direct bodies. This is not a
global fallback census or a claim that the reused generic route is complete.

Four actual producer axiom profiles remain byte-identical to the integrated
baseline: explicit colon 5, compact opener 7, ordinary sequence completion
48 and mapping-value completion 48. None of those four profiles contains
`sorryAx`. The complete failed module and capstones are not promoted from
these local checks. `VerifyDiagnostics.lean` checks exact residual sets,
byte-identical caller types, supplier audits, profiles and escape-reference
comparisons from the saved compiler evidence.

## An initialized consumed-owner sibling

```yaml
? ? a
  : b
  : c
: d
```

Actual initialized scanner observations distinguish:

| Colon | Owner column | Before marks | After marks | Existing source |
| --- | ---: | --- | --- | --- |
| First inner value | 2 | `[0,2]` | `[0]` | Non-stamping |
| Inner sibling | 2 | `[0]` | `[0]` | Stamping |
| Outer value | 0 | `[0]` | `[]` | Non-stamping |

A kernel-checked counterexample constructs a valid cover `[0,2]` for the
actual state after the first colon while proving that column 2 is unmarked.
The initialized grammar proof constructs the root and compact-question
context, consumes the first value, spends the still-open mapping frame on
an actual `emptyKeyNode` sibling and non-nil tail, and then consumes the
surviving root's value to EOF. It assumes no enclosing route and excludes
earlier whole-source witness shortcuts.

| Audited root | Dependency constants | Missing references |
| --- | ---: | ---: |
| Live landing owner | 4,693 | 0 |
| Incoming stored step | 4,238 | 0 |
| Cover does not imply ownership | 5,820 | 0 |
| Consumed sibling then ancestor, to EOF | 6,210 | 0 |

Every root uses only `propext`, `Classical.choice`, `Quot.sound`. Audits
exclude `scannerDrop`, `implicitContinue`, `dropClose`, `sorryAx` and prior
whole-source shortcuts. The finite grammar witness and scanner observations
do not establish reachability of every informative invariant arm.

Controls cover 104 source/budget combinations, including fuel 0/1/2,
empty/root/nested, implicit/explicit, properties, flow, consumed-owner siblings
and BOM input; 40 observed block-value events have no ownership violation.
The first driver consumed BOM unconditionally. Its failed expectations,
source and correction to the real conditional BOM seed are retained.

## Qualification, reproduction and residual

Lean 4.36.0, compiler `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
The inherited 18-module research chain was replayed against the matching
accepted library. Seven relevant standalone modules, including the new
controls/proofs/audit and reused ownership/composition dependencies, also
pass against frozen qualified #392 source
`bea84871310b2b00518629638607bd46f7a2ebba`. The four dependency audits have
the same results there. This establishes standalone compatibility, not
migration of the experimental producer patch onto that owner tree.

Final diagnostic source SHA256:
`1ac1a6dabde77ffe99f7dc5767d042541204ca3b7be90b93c023914d57646982`.
Run `bash Research/R2ColonSupplier/reconstruct.sh` to restore and hash-check
the parent and four new source variants in a disposable directory. Optional
`--compile` uses `R2_BASE_LIB` and `R2_LEAN_BIN`, without producing an accepted
production object. Run the pinned Lean binary with `--run` on
`Research/R2ColonSupplier/VerifyDiagnostics.lean` to verify the saved receipts.
Compressed logs are read directly by that verifier through `xz`.

The next residual is `R2_COLON_ENTRY_SUPPLIER_CLOSE`: the remaining general
close paths still project the whole family away from their pointwise
`h_vpack` interface. The landed-sequence family and the other original
continuations remain separate. The new eligibility and supplier helpers are
**REUSABLE** within their declared scope; full migration remains
**CANDIDATE / UNKNOWN**.

Only research evidence is published. Accepted production source is restored
unchanged. No runtime, guard, ceiling, production ref, native qualification,
hosted workflow, binding/documentation build, owner approval, merge or
maintainer message is changed or initiated. Existing parent census failures
are not repinned or represented as a successful repository qualification.
