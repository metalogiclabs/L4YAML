# Exact seven-byte annotated-grammar decision

Date: 21 November 2026 (New Zealand).

**WARRANTED locally: the frozen native scanner accepts the exact seven-byte
input, while the corrected annotated grammar has no complete trace for it.
REJECTED: universally scanner-qualified S3 for this exact combination.**
Hosted qualification must be read from the run of this branch's actual commit;
this report does not claim an unobserved hosted result.

## Source and statement boundary

The library is the frozen research baseline
`e389fcb62b95b9da954bd81c14427d56e3417dfd`, retained at the immediate experiment
parent `5ac2106405fc45078e36b37d092c09bcfd1fff76`. This change adds a test proof,
corrects an unproved test question's string literal, and supplies its workflow
and report. It changes no scanner behavior or library grammar production.

The source bytes are `3f 20 2d 0a 20 20 3a` (no final newline):

```text
? -
  :
```

`Tests/Guards/Proofs/ColonAnnotatedDecision.lean` pins the character list and
seven-byte size. Its major results are:

| Declaration | Checked conclusion |
| --- | --- |
| `exact_body_has_no_trace` | For every event list `ev`, `¬ TraceOf exactInput ev`, including every possible terminal column. |
| `exact_scanner_accepts` | `∃ ts, Scanner.scanFiltered exactInput = .ok ts`, proved by kernel `cbv` and case analysis. |
| `universal_scan_trace_refuted` | Negation of `∀ input ts, scanFiltered input = .ok ts → TraceOf input (TokenEvents.tokenEvents ts)`. |

The final statement uses the actual scanner and token-event fold. Its negative
conclusion is not inferred from token-parser refusal, or from exclusion of just
one proposed derivation.

**Version distinction:** this research baseline's
`TLYamlStream.implicitContinue` requires `TOpt TLExplicitDocument`. Upstream
integration commit `14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f` still uses
`TOpt TLAnyDocument`. A positive two-bare-document witness for that older
constructor and this negative result concern different grammar declarations.
Do not transfer this refutation across that difference without rechecking it.

## Structural proof

The proof follows the grammar constructors and retains their actual source and
indentation indices. Every root `TBlockNode 0 .blockIn` on this source ends
at one of two positions: the original start (`p0`) or the beginning of the two
spaces before the colon (`p4`). The compact-sequence key ends at `p4`; its
child cannot consume the colon at index two, and an enclosing index-zero
explicit value cannot start there.

The stream's prefix, suffix and explicit-document continuation constructors
cannot advance beyond either frontier. Induction over every `TLYamlStream`
derivation therefore preserves this frontier, which excludes a complete
endpoint `⟨[], col⟩` for every `col`. No parser-completeness assumption,
`scannerDrop`, arbitrary grammar witness or external executable grammar is used.

## Verification and controls

Repository toolchain: `leanprover/lean4:v4.35.0`.

```bash
lake build Tests.Guards.Proofs.ColonAnnotatedDecision
lake build Tests.Guards.Proofs.TwoBareSurfaceWitness
```

The first command passed locally with **40/40 build jobs**. Its four printed
major declarations (`empty_trace_control` and the three above) each have exactly
the standard axiom set `[propext, Classical.choice, Quot.sound]`: no `sorryAx`,
custom axiom or `native_decide` leaf. The empty stream supplies an annotated
positive control. The retained `TwoBareSurfaceWitness` is a separate positive
control for the broader source grammar, without `scannerDrop`. Its local replay
passed **14/14 jobs**, with all three printed declarations depending only on
`propext`.

`.github/workflows/colon-annotated-decision.yml` installs the toolchain from
`lean-toolchain`, records the actual commit/tree and Lean/Lake versions, and
builds both explicit targets. This is a targeted proof qualification, not a new
claim of full repository regression or global YAML conformance.

## Corrected longer-input question

The previous `FullStreamQuestion` used doubled backslashes, denoting literal
backslash-plus-`n` characters. `ColonTwoBareDocuments.lean` now defines
`fullStreamInput` with real line feeds and guards its exact 27-byte list:

```lean
"? -\n  :\n...\n%YAML 1.2\n---\ny"
```

The corrected question is still **unproved**. Existing half-document and
second-explicit-document exclusion proofs remain intact and `propext`-only.
The seven-byte full-stream result suffices to refute universal S3; it does not
by itself refute the longer directive-route certificate.

## Failure lineage and remaining obligations

Earlier broad dependent grammar inversion was inconclusive. This experiment
replaced it with the bounded source-frontier invariant, reusing the proved flow
head restrictions and explicitly checking every block/document constructor.
Local elaboration failures included a module-header placement, redundant case
commands after dependent inversion had already closed a branch, and an opaque
`Except.isOk` expression in the impossible error case. The final native proof
rewrites the actual scan equation, reduces that case to `false = true`, and
eliminates it. Failed elaborations were not admitted as proof evidence.

This result does **not** establish the 27-byte directive-bearing nonmembership,
global `hRoute`, Row 12 removal, S4/coherence, Group 7.7, or whole YAML conformance.
It does not prove that scanner hardening preserves every valid acceptance, or
that parser-qualified S3 suffices for the capstone's reverse direction. It
requires repairing or replacing the rejected runtime/statement combination
before further work may honestly claim to prove this universal S3 target.
