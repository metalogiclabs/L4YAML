# Actual survivor schedules: composition passed, supplier still open

**WARRANTED, bounded:** all 186 initialized scanner/parser controls pass,
including 126 rows missing from P145's contiguous schedules. Lean accepts
the four-entry composition and the mixed consumption/omission composition.
The strict retention migration remains **UNKNOWN**: exactly the same 22
labelled continuation demands remain, with no additional type errors.

Parent: `3cc965918efdc3af9d3f12a2e1a7d14cab8c7f13`, tree
`5165eb6da716567a1fdb4cdfacc108b6301a0060`; Lean 4.36.0. This evidence
commit adds only research files. Production proofs, runtime, guards and
existing PR branches are unchanged.

## What the new source controls establish

P145 tested compact question depths 2–6, three value shapes and contiguous
descending owner schedules. It could omit inner values before the first
value landed. It did not test omitting an intervening value after an earlier
value had already been consumed.

`ScannerControls.lean` enumerates every nonempty descending subset ending
at root 0 for those depths: 62 schedules, with scalar, flow and sequence
values. All 186 sources parse; the indexed parser returns identical complete
documents. The instrument starts from the real scanner seed and uses its
actual preprocess and dispatch functions, with the public scanner's fuel
budget. It checks all 573 explicit colon landings, their actual owners,
prepared owner membership, exact surviving marks, consumed-own exclusion
and strict ancestor bounds. It does not observe Prop-valued proof choices.

| Check | Result |
| --- | ---: |
| Existing P145 source rows covered | 60 |
| Additional source rows | 126 |
| Total accepted rows, both parser implementations | 186 |
| Actual explicit colon landings checked | 573 |
| Refuted expectations | 0 |

Three minimal controls expose the omitted transition:

| Source | Actual colon owners | Key observation |
| --- | --- | --- |
| `? ? ? a` then values at 4 and 0 | 4 / 0 | After consuming 4, mark 2 survives; the next landing drops 2. |
| `? ? ? ? a` then values at 6, 2 and 0 | 6 / 2 / 0 | After consuming 6, marks 0/2/4 survive; the next landing drops 4. |
| `? ? ? ? a` then values at 6, 4 and 0 | 6 / 4 / 0 | Mark 2 is omitted after two inner values have been consumed. |

Complete source strings and before/prepared/after mark lists are in
`logs/scanner-controls.log`. These are finite native observations, not a
universal scanner theorem or a new parser defect.

## The grammar composition works for the mixed case

`MixedComposition.lean` uses the already accepted
`explicitEntryValueRoute` and `compactEntryRoute`. One check retains all four
future values. The mixed check consumes the inner value, then completes
the omitted middle entry using `SBlockMapEntry.explicitEmpty`, while leaving
two outer values available. The omitted entry ends only after its actual
key, including the consumed inner entry's value, completes. It uses the
actual question literals and grammar indices. Wrong-question and wrong-index
applications must fail to elaborate.

Compiler exit 0; both consumed helpers have no axioms. This checks a
conditional composition contract. It does not construct the needed entry
contexts for all reachable scanner states. The existing six affected
production axiom profiles replay byte-identically to the parent receipt
(SHA256 `4d8408ae7595e89a34945111bd5e5367d0be21220a6e13741f638bf72b60f5e5`).
Focused production baseline: 241 jobs, exit 0.

The fresh capstone-path reading on the unchanged accepted source is 252
optional positions, 7 ON, 178 OFF and 67 unresolved; the exact roster is in
`logs/capstone-path.log`. Its `pack-declines: on=0 off=0` also occurred in
the retained parent baseline and is not a new payment.

## Narrower contracts do not pay the missing suppliers

The separate failed diagnostic starts at upstream `9f1f7bc6`, applies the
parent's `retention-original.patch` and `retention-strict-delta.patch`, then
this directory's `retention-refinements.patch`.

Two refinements are tested together:

1. `colon_open_map_explicit` demands `R2KeyPairAt` only under its actual
   `h_noOwn` branch. Its one supplied caller and two open callers are migrated
   explicitly. Both open caller goals now contain consumed-own exclusion.
2. Five property-key writers use `markedCols s'` as their output cover.
   Existing cover proofs transport the single routes; pair demands are
   restricted to actual output marks rather than surplus cover columns.

The compiler accepts the changed colon helper. Its axioms remain the three
standard axioms and the same two inherited `dispatchBlockValue_full_prod`
native-decide axioms. Its profile contains no `sorryAx`. The surrounding
variant does not compile: exit 1, 22 labelled demands, zero other errors.
Every label matches the prior strict diagnostic. The five property goals now
quantify actual output marks, but remain unsolved.

| Residual class | Before | After |
| --- | ---: | ---: |
| Key writers: surviving owner / no chain / no question | 9 | 9 |
| Other colon callers | 2 | 2 |
| Retention at closes, properties, empty values and union | 11 | 11 |
| Additional type errors | 0 | 0 |

No new optional fallback, axiom, detector change or ceiling change is used.
Narrowing alone is rejected as a sufficient repair; the contracts themselves
are not refuted. No impossibility claim follows from labelled `fail` sites.
No critical-position retirement is claimed.

## Consequence and next decisive target

The new controls require continuation preservation to survive consumption
and later omission, not just reach the first colon. The existing result
parameter can express this conditional composition; the actual invariant
still lacks its supplier. Test that supplier at
`accum_content_on_pendingMapValue_indented` after an inner explicit value,
starting with the 4/0 and 6/2/0 controls. Preserve the actual question's whole
entry context through `colon_open_map_explicit` into `pendingMapValue` and
through scalar-value completion. Require the resulting context for the
surviving entries; an isolated composition or another conditional relay is
not a payment.

Parallel #384/item 541 qualification is separate. No new hosted run, merge,
approval attempt, message to maintainers or production ref update occurred.
Early dependency-not-ready and native-instrument elaboration/layout failures
are retained as development evidence. They are superseded by the successful
313-job native build and exit-0 native run, not mathematical refutations.

## Reproduction

On this source with its pinned toolchain/manifest:

```sh
lake build L4YAML.Proofs.Production.StreamAccum L4YAML.Proofs.Production.DocumentProduction
lake env lean Research/R2SurvivorDomain/MixedComposition.lean
lake env lean Research/R2EntryPreservation/AxiomAudit.lean
```

Temporarily add this target to `lakefile.lean`, build it, run the binary and
restore the original lakefile. No target registration is part of the patch.

```lean
lean_exe «r2-survivor-controls» where
  root := `Research.R2SurvivorDomain.ScannerControls
  allowNonModules := true
```

```sh
lake build r2-survivor-controls
.lake/build/bin/r2-survivor-controls
```

For the separate diagnostic, use a disposable checkout of exact `9f1f7bc6`.
Apply the two prior patches in the order above, then the refinements. Its
expected SHA256 is
`578f4fb5803a3ac74d6ff40265db3bd78fec577bd5dad7c53b977f758de76500`.
Run `lake env lean -j 1 L4YAML/Proofs/Production/StreamAccum.lean` with the
matching imports built. Expected exit 1 and the exact roster in
`retention-result.json`. A successful evidence-capture wrapper cannot turn
that failure into a passed retention proof.
