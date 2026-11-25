# Anchored explicit word assurance

Local proof and controls passed on exact NASA/JPL owner source
`0dbf0c120601fccc1d837025f3bef405cc4f2062`, Lean 4.36.0. Independent hosted
qualification is CANDIDATE until its exact jobs, logs and archives pass.

The source family is exactly `? key\n: &a value`, with no trailing LF.
`key` and `value` are arbitrary nonempty lowercase ASCII words; there is no
length bound. The final `anchored_word_assurance` assumes only these two
independently defined word predicates. It proves together:

- Actual initialized `scanLoop` over five real transitions, for every remaining
  fuel, and successful `scanFiltered` with all nine positioned tokens and their
  exact scalar and anchor payloads.
- The raw serialization tree retains the value's `anchor := some "a"`;
  `parseYamlSingle` returns the precise composed block mapping with the anchor
  annotation removed. `document_word` also fixes the raw anchor table to the
  plain value word.
- The actual token event list is exactly `[defineAnchor "a"]`, and the owner's
  independent annotated grammar derives the complete source with that trace.
- The returned scanner registry is exactly `#["a"]`; its offset is the input's
  byte length and its next step is `ok none`.

No scanner-success admission, supplied scanner state, branch guard, grammar
oracle, slot, event transport or EOF premise appears in the final lemma.

## Evidence boundary

The direct grammar construction is independent of scanner acceptance. Its
induction reads the source words and constructs the grammar productions. The
native execution proof reuses the qualified word-scanning induction and weakens
the initialized prefix's old suffix-letter premise to **an arbitrary suffix**.
It then proves the real anchor-dispatch validation and registry update, value
scanning, filtering, payloads and EOF.

All 16 exported proof closures are checked against only `propext`,
`Classical.choice`, and `Quot.sound`. The new final trace and assurance have
**zero inherited native assertions**, improving on the parent's 45-assertion
grammar closure. This does not re-prove or invalidate the parent's other work.

Before proof, 724 native source cases passed exact token-position, payload,
raw/composed parsing and EOF checks. They include explicit key widths
1023/1024/1025/2048, two malformed-property refusals, three corrupt-event
expectations, and scanner fuels 0/1/2/5/6. The controls are imported by the
owner's adversarial-instantiation module in the fresh hosted workflow.

Parent evidence is `afdab55ae7d6a4da04e987a33706d4f6faeff920`
(`research/explicit-word-fragment`), independently qualified in run 45582970898.
`PrepareParent.lean` reconstructs its exact generated proof sources from the
frozen parent workflow and copies the source-controlled word proofs. That
workflow's SHA-256 is pinned; `source-sha256.txt` fixes this extension's sources
and workflow. No owner library, grammar, toolchain or dependency pin is edited.

The hosted matrix checks both the exact #377 proof owner above (library tree
`0a8d15505cf2520df980bc4af05eca0ad72f86c8`) and current upstream
`e7b4eabe764f46f9dfcfd049e77444e6cf0ce6ca` (library tree
`19f54b7a36b0b170aa24375889ff86196e7fa475`). The latter's added declarations
must not be mistaken for an already completed port before its job passes.

## Residual

This proves one unbounded source family against the owner's annotated grammar.
It does not prove universal `scan_trace`, Group 7.7, an independently audited
equivalence with the entire normative YAML grammar, schema resolution, bindings,
arbitrary anchor names, aliases, tags, nesting, or altered whitespace.
Earlier grammar/specification counterexamples and open obligations remain.

The next consequential extension is a later alias using this actual retained
anchor registry, with the same nonempty event trace and exact composed payload.
The broader remaining proof needs a compositional reachable-state invariant
covering properties, nested frames, directives and stream closure.
