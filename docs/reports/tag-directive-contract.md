# Duplicate TAG directives: a requirement erased by the event projection

Date: 21 November 2026 (Pacific/Auckland).

## Finding and scope

On NASA/JPL integration `14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f`, the actual
legacy parser accepts two identical TAG directives for the same handle in a
single document. YAML 1.2.2 section 6.8.2 explicitly forbids that repetition,
including when the prefixes are equal.

The complete production `L4YAML` subtree is unchanged:
`4197c0b6f2fb369e9806ca486d38aef87b077c81`. This branch adds test proofs and
their qualification only; it is not a runtime repair.

Primary normative source:
<https://yaml.org/spec/1.2.2/#682-tag-directives>, restriction following [88]
and Example 6.17. The formal per-document `List.Nodup` requirement in the
experiment is our explicit transcription of that restriction. Lean checks the
formal statements; the correspondence with the external text is an independently
reviewable specification interpretation.

## Exact pair

The single-declaration control has 15 UTF-8 bytes, with one actual LF:

```yaml
%TAG ! !x
--- a
```

The duplicate has 25 bytes, with two actual LFs:

```yaml
%TAG ! !x
%TAG ! !x
--- a
```

Neither input has a trailing newline. The required outcomes for this particular
rule differ: the single declaration is permitted and the duplicate is forbidden.

## Checked statements

`Tests/Guards/Proofs/TagDirectiveContract.lean` uses actual
`TokenParser.parseYaml` and `Scanner.scanFiltered`, not a reimplementation.
Kernel reduction proves:

- both parser success bits are true;
- both actual scanner event projections are `some [beginDocument]`;
- the actual parser retains one handle `[["!"]]` for the control and two
  handles `[["!", "!"]]` for the duplicate;
- the former satisfies the explicit per-document uniqueness requirement and
  the latter violates it;
- successful parsing therefore does not guarantee that requirement;
- no Boolean decision procedure receiving only the unchanged event projection
  can accept the first input and reject the second.

`Tests/Guards/Proofs/TagDirectiveAnnotated.lean` independently constructs
`TraceOf` witnesses for both sources with `[beginDocument]`, and proves the
common trace is serialization-well-formed. Both derivations use
`SLDirective.tag`, `TLDirectiveDocument`, and `TLYamlStream.single`.
They use neither `implicitContinue` nor `scannerDrop`, and assume no scanner
or parser success. Consequently, the Row 19 implicit-continuation correction
cannot remove this single-document derivation.

These are constructive trace witnesses, **not** universal `TraceWellFormed`
theorems for these two inputs. The impossibility theorem concerns the actual
event projection, not every possible source predicate or future contract.

All decisive axioms are within `propext`, `Classical.choice`, and `Quot.sound`.
Some elementary requirement and common-trace lemmas use fewer or no axioms.
There is no `sorry`, new axiom, or `native_decide` proof leaf.

## Existing checks already exercise the mechanism

### The existing completeness consumer requires acceptance

`Tests/Guards/Proofs/TagDirectiveCompleteness.lean` strengthens the admission
result on the same unchanged upstream library. It kernel-checks the actual
scanner output, proves `TokenGrammar` and `TokenStateOk` for those tokens,
and applies the production `parseStream_accepts` theorem with both premises
discharged. The theorem therefore requires acceptance of the duplicate input.

An independent token projection retains explicit directive handles and proves
their uniqueness requirement false. Two checked countertheorems show that no
replacement token parser can retain the original two-premise completeness
contract while rejecting this stream or enforcing this uniqueness condition.
The targeted local build passed 66/66 jobs, with standard-three axiom profiles.

This is a specification boundary of a valid theorem. A token-parser repair
must narrow the admitted token contract as well. A scanner-only repair could
instead narrow which arrays reach the token parser while retaining the more
permissive raw-token API. Neither result says the Lean theorem is unsound or
that every future source-level Group 7.7 contract is impossible.

At the pinned upstream source:

- `Tests/AdversarialInstantiation.lean`, Priority 55, includes two `%TAG !t!`
  declarations in one document with different prefixes and expects parser
  and semantic-checker success.
- `Tests/Guards/Proofs/TokenEventExtractors.lean` includes the same input in
  `agreeing` and explicitly discusses duplicate-directive agreement.
- `L4YAML/Proofs/Serialization/TokenEvents.lean` intentionally removes builtin
  `!` and `!!` handle declarations. Named declarations remain in the list,
  but the current semantic checker permits repeated declarations.
- `EVENTSOF-CONCEPT.md` scopes the stateful acceptance inventory to the
  existing undefined-alias and undeclared-handle error families.

Thus the new finding is the mismatch with the external requirement and its
information-loss mechanism. The duplicate-input class was already tested.
Those tests establish internal agreement; their expected acceptance does not
establish compliance with the external duplicate-directive rule. No claim is
made that every historical issue or conversation was searched.

## Controls and repair implications

The executable grid includes empty input, one declaration, duplicate primary
and secondary handles, duplicate named handles with equal and different
prefixes, two distinct handles, reuse of the same handle in separately
terminated documents, and duplicate YAML-version directives. The first eight
currently parse; duplicate YAML-version directives are already refused. The
equal-event collision is specifically the primary-handle pair; named duplicate
declarations are retained as repeated events but currently accepted by the
checker.

The missing condition can be allocated to an independently specified source
predicate, to a directive-validity predicate, or to richer semantic events.
It does **not** follow that every future Group 7.7 contract is impossible.
`ExactSurfaceLanguage` could independently distinguish the two inputs. A
faithful acceptance guarantee would then also require runtime rejection of the
duplicate.

A parser-side uniqueness guard would affect the ordinary and indexed
`prepareDocumentState` boundary and the premise of `parseStream_accepts`:
the present token grammar and token-state condition admit duplicate directives.
A scanner-side guard is another possible allocation, with a different scope
for direct token-parser callers. Choose and document that allocation before
claiming a complete repair.

Preserve one explicit builtin-handle override, two different handles, legal
per-document redeclaration, repeated tag uses, and anchor-name rebinding.
Default builtin availability is not an explicit declaration.

## Reproduction

Use the repository's pinned Lean 4.35.0 toolchain:

```sh
lake build Tests.Guards.Proofs.TagDirectiveAnnotated Tests.Guards.Proofs.TagDirectiveContract Tests.Guards.Proofs.TagDirectiveCompleteness
```

The dedicated workflow asserts the unchanged production-tree identity, prints
the proof-file hashes and theorem axiom profiles, and preserves its build log.
The local targeted build completed successfully with 39/39 jobs on Lean 4.35.0.
This targeted evidence does not claim full repository qualification, indexed
or FFI equivalence, global grammar completeness, or an upstream repair.

Initial standalone probes lacked the module-system meta import required for
executable controls; that elaboration failure was repaired without modifying
production code. It was an infrastructure failure, not a mathematical verdict.
