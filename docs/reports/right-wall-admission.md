# L4YAML right-wall admission: exact grammar versions and real consumers

Date: 21 November 2026 (Pacific/Auckland).

## Objective and current decision

Determine whether the proposed scanner-wide `scan_trace` theorem is true on
the frozen research source and whether that exact strength is necessary for
Group 7.7. Keep the normative YAML contract separate from scanner acceptance.

This report is an admission experiment, not a claim of Group 7.7 completion.
No library production or executable is changed on this branch. All new Lean
files are explicitly built test modules; the workflow prints their exact
source/tree and axiom profiles.

## Source identities

| Snapshot | Exact commit | Annotated implicit continuation |
| --- | --- | --- |
| Owner integration | `14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f` | `TOpt TLAnyDocument` |
| Frozen unpatched research library | `e389fcb62b95b9da954bd81c14427d56e3417dfd` | `TOpt TLExplicitDocument` |
| Existing source witness, same research library | `5ac2106405fc45078e36b37d092c09bcfd1fff76` | `TOpt TLExplicitDocument` |

The source-side `SLYamlStream.implicitContinue` still takes
`GOpt SLAnyDocument` in both library snapshots. Therefore the upstream
annotated grammar and the frozen research annotated grammar are different
mathematical targets. The latter must not be described as the upstream one.

The owner integration and release branches were independently read back as
`14eb6dba` and `122064d0c853be8d6c2f4cd255c6fcd67acc4ae8`, respectively.

## Exact input and upstream decision

The body is exactly seven UTF-8 bytes, with one LF and no trailing newline:

```text
? -
  :
```

Hex: `3f 20 2d 0a 20 20 3a`.

`Tests/Guards/Proofs/UpstreamColonTrace.lean` constructs the complete
upstream annotated derivation:

```lean
lemma traceOf_seven_bytes : TraceOf input []
```

The proof starts at the actual input's `toList`, ends at the empty suffix
with column 3, and joins two bare documents through the actual upstream
`TLYamlStream.implicitContinue`. It does not use `scannerDrop`, scanner
acceptance, parser acceptance, `sorry`, a new axiom, or a reflected proof leaf.
The structural construction has only `propext`; the final string-indexed
declaration has Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The negative control proves that the second document has no
`TLExplicitDocument` derivation. The positive control is the empty stream.
`UpstreamColonRuntime.lean` separately checks the native tuple
`(scanner succeeds, scanner events are empty, token parser refuses)` is
`(true, true, true)` on the same exact body. The combined targeted build
completed successfully with 38 jobs on Lean 4.35.0.

This is a positive answer for the upstream grammar, not a refutation of S3
on that grammar. It does not establish `TraceWellFormed input`: that
predicate quantifies over every possible trace, not just the constructed one.

[YAML 1.2.2 section 9.2](https://yaml.org/spec/1.2.2/#92-streams) requires a
separation marker between successive documents. Production 211 does not
have an unseparated second-bare-document arm. The construction demonstrates
the existing Row 19 mismatch concretely; the repository's blueprint and
DOCS already identify that over-approximation and its required narrowing.
This is not evidence that the maintainers were unaware of Row 19.

## Frozen research grammar decision

The separate `ColonAnnotatedDecision.lean` experiment on the unchanged
research library proves nonmembership for **every event list and EOF
column**. It uses a finite endpoint invariant over actual grammar
constructors: a stream beginning at the seven-byte source can end only
at its start or the start of the colon line; neither is EOF.

The nonmembership theorem was checked by Lean 4.35.0, then composed with
kernel-reduced native scanner acceptance in a successful 40-job targeted
build. All four headline declarations use only the three standard axioms. No parser
rejection premise, weaker source grammar, or unproved helper supplies it.
The final declaration `universal_scan_trace_refuted` negates exactly
`∀ input ts, scanFiltered input = .ok ts → TraceOf input (tokenEvents ts)`.
Its witness is the same seven-byte body, with the actual scanner token array.
Therefore this universal claim is **REJECTED on the frozen combination**.
The separate [proof-decision commit e94baa39](https://github.com/metalogiclabs/L4YAML/commit/e94baa39f828852390ff65f9441c4bb4253b9cfc),
tree `dd733c2157ba189c060412ff73809cd84a0700b0`, preserves the exact source
and hosted workflow. The locally checked tree equals the hosted tree.
This does not refute S3 on the already patched scanner.

The earlier `ColonTwoBareDocuments.FullStreamQuestion` was only an unproved
definition and accidentally contained literal backslash-n pairs. Its
proved `SurfPos` lemmas already used actual LF characters. The placeholder
has been corrected to the intended **27-byte** directive-bearing string
and bound with a byte/content guard. That correction does not itself decide
the extended input or universal directive-route reachability.

## Group 7.7 consumer audit

The authoritative `Blueprint/04-capstones.md` says `ExactSurfaceLanguage`
and the final `parse_iff_grammar` converse are not yet declared. There is no
completed capstone declaration whose dependency graph can establish the
desired external claim. DOCS item 454 supplies a proposed composition.

`Tests/Guards/Proofs/AcceptedTraceContract.lean` makes that composition
explicit against the actual implementation and exported proof interfaces:

1. **Forward serialization:** successful legacy `parseYaml` factors into
   successful `scanFiltered` and `parseStream`. A trace bridge qualified by
   those two successes supplies the scanner's source trace. The existing
   `scanFiltered_parseStream_ok_checkFrom_full` supplies its serialization
   well-formedness. An explicitly unpaid coherence premise carries that
   validity to every grammar trace, giving `TraceWellFormed`.
2. **Reverse acceptance:** the missing source-side producer must construct
   successful scanning, `TokenGrammar` for those same tokens, and a
   `TraceOf` witness for their actual events. `TraceWellFormed` then supplies
   `TokenStateOk`, and the existing `parseStream_accepts` and pipeline
   composition give acceptance. No parser-success premise is assumed.

Thus scanner-only S3 is stronger than the documented forward serialization
consumer needs. A parser-qualified replacement cannot be used to establish
parsing in the reverse direction: that would be circular. The reverse
composition does not require trace uniqueness once the actual trace
certificate is supplied; coherence belongs to the chosen forward route.

These are **conditional sufficiency checks**. They do not prove the trace
bridge, coherence, the reverse certificate producer, exact surface language,
or Group 7.7. They identify exactly which producer work remains.

The actual consumer module completed its targeted build successfully:
147 jobs on Lean 4.35.0. All three composition lemmas have exactly
`propext`, `Classical.choice`, and `Quot.sound` as their axiom dependencies.
There is no `sorryAx`, custom axiom, or reflected proof leaf in them. The
empty stream, exact seven-byte scanner/parser mismatch, and scanner refusal
of the undeclared alias `*x` are executable boundary controls in the module.

The separately declared Group 7.6 `scan_strict_proof` still promises
`scan input = .ok tokens -> InYamlLanguage input` and is registered as a
capstone. Restricting Group 7.7's serialization bridge does not retire that
independent scanner-wide obligation or authorize silently weakening it.

The tested composition names the **legacy** `TokenParser.parseYaml` API.
The public FFI safe entry point invokes the indexed safe pipeline and
enforces configurable limits. Claims about that API additionally require
the matching correspondence and an explicit limits policy. Schema/value
resolution and FFI fidelity are also distinct from this language result.

## Completed scanner-repair qualification

[Actions 44795032978](https://github.com/metalogiclabs/L4YAML/actions/runs/44795032978)
is now SUCCESS at `1b8eba9732cc96b86dd77cdcc40e8cf2cac78767`, tree
`c74c3c2e862533714e56c206d8bf6e96123ca9ec`:

- Full repository build: 1,571 jobs.
- Protected assertions: 62,260 / 62,260.
- Ordinary full regression: completed, report aggregate 64,419 / 64,419.
- The non-default `tests`, `demo`, and `limittests` executables were
  explicitly built before running them.

Complete recursive tree comparison with review head
`bbeb673df9dc9242a7bcb6c2c58a2cdcdfda35e0` finds only one differing leaf:
the qualification workflow. All other source, test, dependency, and
submodule entries match by path, mode, type, and SHA. This qualifies the
review-ready source for the stated bounded suite; it does not prove
universal preservation of valid YAML or global grammar correspondence.

The separate experimental repair at `6ce5e324` had 1,573 build jobs.
Those counts refer to different trees and must not be conflated.

## One-field source tightening: predicted and measured consequence

The isolated price experiment changes only the source `implicitContinue`
premise from `GOpt SLAnyDocument` to `GOpt SLExplicitDocument`, with its
docstring corrected in place. It is based on upstream `14eb6dba`.

Prediction before compilation: `topLevelFlowResumeSep`, `rootMapRoute`,
`rootMapRouteF`, and `bareNodeRoute` must pay a real document-origin or
continuation obligation, because their bodies append bare documents to an
arbitrary prior stream. An explicit-document wrapper site is a mechanical
type change; the four bare routes cannot be repaired by merely removing a
wrapper. Replacing them with `scannerDrop` would preserve the wrong
guarantee and is not an admissible repair.

The first prediction was measured by replaying the **exact type and body**
of upstream `StreamAccum.topLevelFlowResumeSep` in an isolated module.
A textual comparison confirms the copied declaration is unchanged.
The original grammar accepted it (compiler exit 0). The narrowed grammar
itself compiled (exit 0). The same consumer against that narrowed grammar
failed (exit 1), precisely because its `SLAnyDocument.bare ...` has type
`SLAnyDocument sp_mid sp_m`, where `SLExplicitDocument sp_mid sp_m` is required.

The source patch, unchanged consumer, and actual compiler error are saved in
[`right-wall/`](right-wall/). This is a local, exact-body price, **not a full
rebuild of the narrowed library**. The other predicted sites remain a
source-analysis roster, not a measured full failure count. No repair through
`scannerDrop` was attempted. The green branch's library stays byte-identical
to its upstream parent.

An initial isolated-loader attempt lacked the imported `Surface.Node` object
under its alternate module root; that infrastructure failure was corrected
before the type-mismatch measurement. Separately, the native token-event
guard needed a `meta import` to expose the existing implementation to the
evaluator. Neither failure was a mathematical result.

## Remaining decision boundary

Do not expand a global proof of the frozen scanner-only statement once its
checked counterexample is composed. Retain the exact old-source refutation,
the bounded repaired scanner qualification, and the separate grammar-version
decisions. Pay the source/trace document-continuation obligations and choose
the smallest sufficient consumer contract explicitly. The final proof still
owes the normative exact-language definition, remaining scanner/grammar
correspondence, Row 12 retirement, required coherence, and reverse producer.

No upstream pull request, merge, or collaborator message is part of this
experiment.
