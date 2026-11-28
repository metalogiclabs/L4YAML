# The saved family funds the landed sequence

Heath Sanchez · 2026-11-28

**WARRANTED, bounded / REUSABLE.** The landed-sequence reader was discarding
information it already received. Reading `h_vslot_saved` funds the actual
`pendingBlock.h_close_entry` family whenever its informative arm is available
and the existing slot index satisfies `nv ≤ k`. The former singleton marked
domain is unnecessary for this whole-family construction.

This complements ownership: excluding the consumed owner does not construct
the grammar continuation of the surviving ancestors. Here that continuation
comes from the saved slot's actual grammar domain, including the sequence tail.

| Check | Observed result |
| --- | --- |
| Original accepted-library replay | 22 research modules checked |
| Initialized landed witness | Two ancestors, nonempty current sequence tail, both values consumed to EOF |
| Recursive dependency audit | 6,244 constants; 15 required names; 10 forbidden shortcuts; zero missing references or free route premises |
| Helper and whole witness axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Actual experimental producer | Saved-slot branch typechecks; 23 named residual locations, zero extra type errors |
| Erasure controls | Actual producer and standalone reader both fail at the stream-only interface |
| Inherited profiles | Compact, mapping-value completion and ordinary sequence completion arrays byte-identical to parent |
| Qualified #392 reuse | Five new positive modules checked using the parent's 18 already checked research modules; actual `TopUnmarked` / `h_expl` retained |

The initialized witness is:

```yaml
? ?
    - a
    - b
  : c
: d
```

Kernel-evaluated initialized scanner projections retain `[0,2]` at the first
and sibling dashes, then `[0]` after the inner colon and `[]` after the outer
colon. Presence guards exclude the default-state alternative. The root route
is constructed. The proof applies the landed helper to an actual
`SCompactSeqTail.cons`; it does not borrow an earlier complete-source proof,
use the compact-sequence helper, or use `scannerDrop`, `implicitContinue`,
`dropClose`, `sorryAx`, a custom axiom or an assumed enclosing route.

These witnesses establish availability of a meaningful family on actual
initialized projections. Scanner observations do not reveal which disjunct a
proof chose. A full accumulator invariant reaching this branch is not proved.

The [producer delta](landed-family.patch) introduces no external family premise
and preserves the existing pointwise/frame routing. It spends the saved
family directly at the landed writer. The [erasure delta](erased-family.patch)
changes that actual call to read only the stream projection. The resulting
type error expects `EntryValues` where only `SLYamlStream` remains. This
establishes the dependency of this construction, not impossibility of every
alternative proof.

## What remains UNKNOWN

The old `R2_SEQUENCE_LANDED_FAMILY` failure is **narrowed, not globally paid**:

| Remaining input case | Exact label |
| --- | --- |
| Informative slot exists but `k < nv` | `R2_SEQUENCE_LANDED_LEFT_OF_SLOT` |
| Only the deferred/residue slot arm is supplied | `R2_SEQUENCE_LANDED_MISSING_SLOT` |

All 21 other parent failure locations remain. Splitting one location into two
changes the diagnostic roster from 22 to 23; these are classifications of an
unfinished stronger contract, not a measure of critical proof debt. The whole
experimental module still fails intentionally. No critical position is retired
or remeasured on this failed variant; the last accepted roster remains seven.

The highest-leverage next experiment is to price the actual resumed/value-frame
inputs to these two cases. Determine whether their existing whole-family
continuation can be retained through `h_valFV` / `h_mapFV`, or whether a specific
producer genuinely lacks it. Do not add another conditional carrier before
identifying its actual producer and reader.

## Exact lineage and replay

Parent: [`8d4596f2`](https://github.com/metalogiclabs/L4YAML/commit/8d4596f26cf430df50d0e3f1e0dce2ea1104f83d).
Retains its marked-owner colon result, explicit route dependency, failures and
qualification boundaries. This commit adds only this research directory.

| Diagnostic source | SHA256 |
| --- | --- |
| Parent marked-pair variant | `9b7617d47c6e3a8792bfa659a73238a72dd004195b6e78f3a6b82512ae211b83` |
| Landed positive variant | `23f863a9c49ebd063bb89571c4d3bd2ea2cdf33749b6ffdd3357a7d7ad1b7fcc` |
| Actual-reader erasure | `d055569ab8fe741fc50e529f8c48e52e29081bfd173278ebba3f45b103b29547` |

Qualified owner: `bea84871310b2b00518629638607bd46f7a2ebba`; production-source
SHA256 `695b4080d6086b1d8d78c9459c5c12d9850947be3811cba45fbedd12fd1ad62f`.
The original accepted library's source is
`f1eece1acca9f124666aa8fcc8fe5b591c316df35b292b32ed28af491a25772a`.
Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.

Run `bash Research/R2LandedContinuation/reconstruct.sh` to reconstruct and
hash-check both diagnostic variants. Add `--compile` with `R2_BASE_LIB` and
`R2_LEAN_BIN` pointing to the original matching accepted library and pinned
binary. Run `replay-proofs.sh` with either matching accepted library to rebuild
the 22 standalone modules. Set `R2_CHECK_QUALIFIED_OWNER=1` for the ownership
interface audit. Diagnostic and erasure failures are expected. Run
`lean --run Research/R2LandedContinuation/VerifyDiagnostics.lean` to check the
archived exact error rosters, profile equality and negative controls.

The first optional qualified replay stopped before elaboration because a new
`Research` directory shadowed the parent's module root. Its failure log is
retained. Linking the six unchanged parent module directories into the isolated
output root fixed module resolution; the five-module replay then passed.

No production source, census pin, toolchain or maintainer approval is changed.
No owner CI, native suite, binding suite or documentation build was dispatched.
