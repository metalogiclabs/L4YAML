# Surviving entry domains after an actual consumed value

Source parent: 3cc965918efdc3af9d3f12a2e1a7d14cab8c7f13.
Strict diagnostic source: upstream 9f1f7bc6 plus the two retained patches,
SHA256 1a482089f93091d8d2daafbcdec875c2f64ade131e343ddfe8b11c37186dcbaa.
Lean 4.36.0; no hosted workflow or production ref changes.

Objective: retain the real explicit-entry continuation across a consumed
inner value and the later omission of an intervening owner. Intended path:
entry routes → real colon callers → accumulation → scan_content_gives_stream_v2.

Predictions, written before this round's compiler/native experiments:

1. Enumerating all nonempty descending owner schedules ending at the root
   for compact question depths 2–6 gives 62 schedules, 186 source rows with
   scalar, flow and sequence values. P145's contiguous schedules account for
   20 schedules / 60 rows; 42 schedules / 126 rows are additional coverage.
2. All 186 sources parse. Each actual explicit colon consumes its own mark
   and leaves exactly the strictly smaller question columns. Missing middle
   values may be omitted after an earlier value has already been consumed.
3. The smallest mixed controls have owner schedules 4/0, 6/2/0 and 6/4/0;
   they require different omission decisions despite the same initial key.
4. The existing result-parametric entry helpers can retain four real entry
   contexts, consume one inner value, and then select explicitEmpty for a
   skipped middle entry, while retaining the root's eventual value.
   Wrong-question/index controls must still fail to elaborate. This is a
   conditional composition result, not a reachable-state supplier theorem.
5. Scoping colon_open_map_explicit's pair premise to its actual h_noOwn
   branch elaborates without adding a disjunction. Both other colon callers
   receive h_noOwn in their unsolved pair goal; they need not become solved.
6. Normalizing the five property-key output covers to actual output marks
   eliminates surplus cover columns from their goal. This may narrow the
   demand without discharging it. The nine genuine key-writer demands remain.
7. No critical-position retirement is predicted. A failed diagnostic stays
   UNKNOWN even if its outer evidence-capture command succeeds.

Acceptance: initialized scanner/parser observations with exact landing and
mark expectations; compiler-accepted composition with axiom output; exact
diagnostic labels and type-error count. No full default qualification or
claim of universal retention follows from these checks.
