# Reconciliation with experiments completed in another research thread

The canonical state changed during this local experiment. Two already-running
experiments on upstream PR #387 completed. They are reconciled here rather
than superseded by the earlier source pin of the three-sequence-relay test.

| Existing experiment | Verified result | Unresolved boundary |
| --- | --- | --- |
| Compact question h_explUp writer, run 45968133262 | Actual StreamAccum build exit 0, 239 jobs; four P144 slot guards passed; capstone instrument reports seven ON positions | No retirement; no paired baseline/axiom comparison in archive |
| Universal question ancestor continuation, run 45968167777 | Actual StreamAccum build exit 1, exactly ANCESTOR_DOMAIN and ANCESTOR_NO_CHAIN diagnostics | Global original-entry supplier remains unproved |

Both outer workflows report SUCCESS because they preserve diagnostic exits.
That status is not mathematical acceptance. The second run's scanner trace
also failed, on the undefined identifier `markedColsOf`; its five controls
were not executed successfully in that hosted run.

The artifacts were independently downloaded: 13/13 CRCs for 15184027707,
14/14 for 15183528391. Their SHA256s match provider metadata:

- Compact writer: `9a7d9b1bd927ce8314110dc5196ef65b33058d6012752d7e6768a74b29d18fcb`.
- Question demand: `673ac67afb968dff102923523256f0e36dd7d2c370e0234d17af912e32bdddba`.

Both candidate patches were independently applied to the exact upstream
StreamAccum blob and reconstructed the archived source SHA256s:
`d89a05d0ded19e6d641c139cadeb403c16ae94c245489464eb0af6b5e2b0cc12`
and `17593dabefa0f5c68247393e738cc62f8ee35d495b70fa9314df05351ce5709c`.
The source checkout was restored clean afterward.

The compact capstone log's `pack-declines: on=0 off=0` reading is preserved.
There is no paired same-instrument baseline in its archive. It is not
promoted as three critical payments; the same output still reports seven
critical positions. A fresh comparable census and candidate axiom audit are
required before a stronger claim.

## Trace tooling repaired and replayed on the exact upstream source

Used a separate clean checkout of upstream
`9f1f7bc60cf54741c1bf5d0c0618ee680268ed15`, tree
`0c7dced413db0510b0a0a144ca2ca74111cf6a77`, with Lean 4.36.0.
The scanner, parser, token, spec and both event emitter source directories
are identical to the local test pin; RegisterWitness differs by proof-only
additions and its markedCols definition is unchanged.

Changed only the failed trace's lookup from
`markedColsOf s.pendingKeys s.indentColumns` to the actual exported
`markedCols s`; original and corrected sources are retained. The targeted
upstream dependency build passed (205 jobs). All five original slot guards
and the successful list/indexed event-stream equality guard over all five
sources now pass locally (exit 0). This repairs the missing control evidence,
not the failed ancestor theorem.

The fourteen-source entry probe also passes on this exact upstream checkout;
its complete JSON trace is byte-identical to the earlier local replay,
including the skipped-inner-question ownership counterexample.

## Combined frontier

Conditional sequence transport and the compact question writer are now
separately evidenced. Neither closes the mandatory ancestor continuation.
The question-producer diagnostic distinguishes a missing covered domain
from a missing chain. The accepted skipped-question control shows that the
needed association is with the entry surviving preprocessing, not simply
the latest question encountered. These are complementary results from
different source pins, not one combined qualified proof.

Next use the original-entry and post-preprocessing marks at the existing
question/key-completion producer. Preserve the compact writer candidate;
do not duplicate its hosted qualification. No production branch, upstream
PR, permission, approval or owner workflow was changed here.
