# Group 7.7: corrected target and source bridge

Status: specification proposal; full theorem UNKNOWN. This is not a Lean
implementation of the complete YAML grammar and does not supersede checked
claims at their original source identities. See `obligations.json` for receipts.

## Two obligations, not one repair queue

Let `Accept s := ∃ docs, TokenParser.parseYaml s = .ok docs`.
Let `ValidSource s` denote an independently defined YAML 1.2.2 presentation
stream with its required document-local serialization conditions.

The intended statements are:

* Completeness (7.7): `∀ s : String, ValidSource s → Accept s`.
* Strictness against that SAME language: `∀ s : String, Accept s → ValidSource s`.

Only both statements establish the intended equivalence. The existing forward
proof into the over-approximate `InYamlLanguage` does not supply the second
statement for a repaired language. Rejecting invalid comments is necessary for
strictness, but is not a prerequisite for the completeness implication.

`ValidSource` must NOT be defined by scanner success, parser success, token
acceptance, emitter images, or a conjunction containing any of those. No such
predicate is declared implemented here. Existing `RepairedStream` is insufficient:
its scalar leaves admit the checked raw-control witness.

## Required independent representation

Derivations must consume exactly the original source from start to EOF and
retain the syntax/context needed for each rule. No disconnected `scannerDrop`,
no skipped spans, no unmarked arbitrary-document continuation. Comments and BOM
prefixes between documents must remain representable. Every leaf must meet its
own normative character/context rules; quoted nb-json is not interchangeable
with comment nb-char. Indentation, flow context, implicit-key limits, escapes,
directive bodies, and scalar boundaries remain obligations, not inferred facts.

Document structure must retain directive declarations before reducing them to
serialization events. Enforce at most one YAML directive and at most one explicit
TAG declaration per handle per document; preserve tag-prefix syntax and required
`---`. Reset scope at the correct document boundary. Reuse
`DirectiveDiscipline.VersionDisciplinedRun` where applicable; it establishes only
version uniqueness on its declared source span, not the whole directive policy.

For serialization, reuse `SerializationWellFormed` for prior-anchor and tag-handle
availability, but derive its events from the SAME source derivation. Do not assume
that an arbitrary well-formed trace belongs to the scanner's tokens. Anchor
rebinding is legal; do not impose global anchor uniqueness or acyclicity merely
to simplify a proof. Directive multiplicity is not recoverable from the current
erased event list (`DirectiveTrace` already demonstrates that loss).

Governing source: YAML 1.2.2, https://yaml.org/spec/1.2.2/ — sections 3.2.2.2,
5, 6.6, 6.8, 7.1 and productions [27], [75], [82]-[93], [107], [211].
The full production inventory and its faithful formalization are still UNKNOWN.
The boundary is Lean Unicode `String` input; byte decoding is outside this API.
This acceptance target alone does not establish decoded-output fidelity.

## Exact missing producer interface

Once `ValidSource` is independently implemented, prove for every source:

```lean
ValidSource input →
  ∃ ts, Scanner.scanFiltered input = .ok ts ∧
    L4YAML.Proofs.TokenGrammar.TokenGrammar ts ∧
    L4YAML.Proofs.TokenGrammar.TokenStateOk ts
```

The scanner-success equation belongs in the CONCLUSION of this bridge, never in
`ValidSource` or as an assumed premise of the headline theorem. Use the actual
public scanner's fuel. Token-state agreement must be established for these exact
tokens, not a separately chosen trace.

The existing `StreamCompleteness.parseStream_accepts` consumes the last two
facts. `TokenParser.parseYamlRaw` and `parseYaml` then compose the scanner and
parser. `QuotedPublic.source_quoted_public_accepts` already demonstrates that
whole-source proof pattern for an independent restricted grammar; reuse it.
This decomposition does not prove the producer or the full source language.

## Retained separators and completion gate

Retain the already checked '[' / '[]' pair; raw U+0001 in quotes versus its escaped
spelling; valid versus duplicated YAML directives with equal erased events;
alias/tag scope controls; and the annotated continuation witnesses. These refute
weaker proposed representations. Passing them is necessary, never sufficient.

The separate normative-comment candidate fixes a runtime strictness defect. Its
full integration remains unqualified. Duplicate TAG acceptance is another known
strictness mismatch, pinned in `DirectiveControls.lean`; do not rediscover it or
claim comments alone restore equivalence.

Next structural experiment: define a source-connected directive/document
judgment retaining version and explicit TAG declarations, with the existing
independent quoted-leaf grammar for the body as a test consumer. Check duplicate
version, duplicate handle, declaration reset, and source-to-token event agreement.
Label this fragment explicitly. Generalize only after the representation passes
those separating tests; neither the fragment nor this document is full completion.
