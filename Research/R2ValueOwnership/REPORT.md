# Actual block-colon ownership pays the marked-own R2 branch

Owner source: `1383fa62e838576fb9c712b4af89b5e381aaaab4` (item 541).
Intended dependency: scanner ownership → `PendingNode.pendingMapValue.h_expl`
→ `accum_block_pending` → capstones 7.3 and 7.2.

WARRANTED bounded: Lean 4.36.0 proves that a successful block `scanValue`
leaves its last pending-key slot unmarked. Existing slot synchronization,
strictly increasing indentation, and the park's upper bound exclude a mark
at the park's own column. Smaller ancestor marks remain allowed. The six
helpers used in production have only the standard three axioms. The actual
consumer spends the exclusion, and a dependency audit reaches all seven
new predicate/helper declarations from capstone 7.2.

The stronger fact is stored in the existing negative explicit-entry face,
beside `NotQuestionPark`; it is not inferred from that token predicate alone.
Every actual colon caller funds it from its successful preprocess and
dispatcher result plus existing soundness and stack monotonicity. The
marked-own decline in the funded ancestor-chain branch is removed. This
does not fund the separate missing ancestor-chain alternative.

The executable sweep preceded the proof: 108 source/fuel runs, 47 observed
value steps, zero ownership violations. The later production-suite port
uses `scan`'s BOM-consuming seed and explicitly pins surviving ancestors,
a non-nil sibling tail, flow observations and a marked-question negative
control. The original research BOM row took no step; the port corrects
that coverage limitation. A full source build and native-suite result are
not yet claimed at this checkpoint.

The nine common producer/capstone axiom profiles are byte-identical to the
accepted continuation source (StreamAccum SHA256
`f1eece1acca9f124666aa8fcc8fe5b591c316df35b292b32ed28af491a25772a`),
combined profile SHA256
`88db00e41d20b29b31c35bfbb015bd8b5095533e517ac926832b47298260c5be`.
That comparison baseline is explicitly different from the owner source.
The current full-build price has exposed the expected new state predicate
in the ghost-index census and an outdated constructor-type fixture.

Production migration and final census impact remain CANDIDATE until the
whole build and declared checks pass. All seven critical positions remain
unretired at this boundary. The parallel `R2CompactSlot` continuation work
is separate and has not been modified. Failed proof and interface logs
are preserved rather than promoted to verification evidence.
