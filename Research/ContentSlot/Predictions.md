# Actual explicit-value columns and the content-slot retirement residual

Owner: cc83019024fb88b7c0d0cdadc4e590bda7a72788, Lean 4.36.0.
This is separate from root-slot PR #380. No production branch is changed.

Objective: retire pendingContent.h_vpack's optional alternative over actual
marked columns. The earlier full-field price found 12 initial failures across
four producer families, not a closure fixpoint. The two content-dispatch births
still receive a vacuous upstream premise; local payment would move that gap.

Cheapest consequential prerequisite: the block consumer currently drops
MarkedColsIn from its input and then permits an off-column escape. Preserve
the state-linked domain and use PendingKeySound.Sound at the actual explicit
value source. The preceding state-linked experiment is reused only for this
consumer correction; its pendingContent re-indexing and root payment are not
part of this candidate.

The restored consumer domain also makes the earlier marker payments meaningful.
Both marker parks carry a dead explicit-key register and the loop's Sound
invariant. Pay the helper with an empty list AND a proof that it covers the
actual scanner domain. This replaces the superseded free-list marker
interpretation, rather than claiming that its old PAY label was sufficient.
The 126 source-initialized marker controls were replayed before this edit:
252 start-marker states and 210 end-marker states, all with empty actual marks.

Before proof construction, the source-initialized control passed 396 accepted
sources and 6102 steps: 1830 marked content steps, 1410 with multiple marks,
72 marked flow closes, maximum 10 simultaneous marks, 1686 explicit values
including 1614 dedent landings. Empty-list covers fail at all 1686 value
landings; singleton cover controls fail at 1290. The permanent Rule-2 cases
are included in Tests/AdversarialInstantiation.lean.

Predictions before full qualification:

1. All three production applications of stamp_offcol disappear, and its
   declaration leaves the scan/parse strictness capstone closure.
2. The new actual-state correspondence lemma is consumed by that closure.
3. The seven existing touched producer/capstone axiom sets are unchanged;
   the new lemma uses only standard logical axioms.
4. The full native battery increases by 792 cases, all passing. Runtime
   scanner/parser sources and dependency/toolchain pins are unchanged.
5. A previous existential chain producer paid an unconnected empty list.
   Requiring a real domain may expose additional DECLINE leaves; retain and
   explain those readings rather than treating all smaller counts as truth.
6. Complete pendingContent field retirement, scannerDrop deletion and universal
   scan_trace remain UNKNOWN. No claim of a numerical tenfold improvement.
7. The two document-marker h_vpack supplies are genuinely paid: the shared
   helper's direct declines fall 3 to 1, and critical-path direct declines
   fall 6 to 4 on this owner without incorporating root-slot PR #380.

