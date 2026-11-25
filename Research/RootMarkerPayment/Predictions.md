# Root and document-marker value-pack payments

Owner: cc83019024fb88b7c0d0cdadc4e590bda7a72788; Lean 4.36.0.

Objective: remove actual capstone-path declines using maintained scanner state,
without importing the mixed state-linked value-pack candidate.

The root payment is retained from independently qualified 920795ed. The next
experiment targets the two marker arms of accum_block_pending. Both already
carry explicitKeyLine = none and PendingKeySound.Sound. Predict that these imply
an empty actual marked-column projection, allowing each existing h_vpack supply
to use Or.inl quantified over RegisterWitness.markedCols sc.

Before the proof change, run real source-initialized marker transitions and check
the actual projection after both document markers, including explicit-key source
history, empty/scalar/collection documents, BOM/comments and LF/CRLF.

Predictions against the owner:

1. Direct relay DECLINE edges: 237 -> 234 (root plus two marker arms).
2. Capstone-path direct declines: 6 -> 3; seven optional positions remain.
3. No new library declaration, ghost index, scanner field or custom axiom.
4. Split-decline and free-decline counts do not grow. Any contrary reading is
   retained, not silently repinned as an improvement.
5. The full library, guards and required gates must build before submission.

Whole-field retirement remains an experiment, not a result. The remaining
pendingFlow supply must not be removed by dropping an existing route.
