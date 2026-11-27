# Full-entry continuation composition

Source: upstream PR #387, commit 9f1f7bc60cf54741c1bf5d0c0618ee680268ed15,
tree 0c7dced413db0510b0a0a144ca2ca74111cf6a77; Lean 4.36.0.

Objective: test whether the grammar continuation can keep the actual explicit
entry open while its compact key is completed, instead of selecting the
key-only alternative before the entry's own value has arrived.

Intended dependency chain: generic explicit-entry and compact-entry routes →
explEntryChain_of_keyContent / compactExplicitKeyFrame / compact_open_map →
accumulation → scan_content_gives_stream_v2 → scan_strict_proof.

Before the implementation:

1. The three-level composition check fails because the generic entry routes
   are absent. Its desired result retains all three future value lines.
2. Sixty initialized scanner/parser sources across depths 2–6, omitted inner
   values, and scalar/flow/sequence values pass 165 new checks. These controls
   precede the library proof edits and cannot observe proof disjuncts.
3. Two helpers, polymorphic in the continuation's result predicate, compose
   all three future value lines without explicitEmpty or a new alternative.
   Wrong source question and wrong entry index fail to elaborate.
4. The existing compact-writer candidate remains valid using this same
   composition, with its actual question literal and transported mark cover.
   Its prior source and qualification are retained, not counted as novel.
5. Existing affected axiom profiles remain byte-identical; both new helpers
   have no axioms. The source runtime and capstone statements are unchanged.
6. No critical-position retirement is predicted. Generic composition does
   not construct the missing family of contexts for all surviving entries.

Acceptance boundary: compiled actual producer and consumer, type-checked
three-value composition and identity controls, paired capstone measurements,
native controls, and axiom comparison. A standalone composition result is
not a universal scanner-context preservation theorem.

Lineage: 85f3188f's three-relay negative and skipped-inner-question control;
compact writer run 45968133262; universal question diagnostic 45968167777.
