# State-linked explicit-value packs — prediction before measurement

Owner cc83019024fb88b7c0d0cdadc4e590bda7a72788; baseline includes the independently
qualified root-key-slot payment at 920795ed5badde6e1b26b77dbf672b9cda01e992.

The two `h_vpack` helper parameters currently forget the `MarkedColsIn sc ns`
cover already carried by their real producers. An arbitrary empty list therefore
inhabits their informative disjunct even when the scanner has pending marks.
Do not count such a witness as progress.

P1: restoring that cover requires only information already present at producers;
no scanner field, invariant premise, admitted proof, or new axiom is needed.

P2: existing `PendingKeySound.Sound`, preprocessing, and the accepted explicit
value's source tests imply that its column belongs to the original state's
marked columns. The three production calls to
`block_dispatch_deferred_stamp_offcol` can consequently be removed.

P3: re-indexing `PendingNode.pendingContent.h_vpack` by `markedCols sc` can remove
one ghost-index row (74 to 73) without weakening any producer's domain.

P4: eliminating the off-column fallback calls reduces its capstone reachability;
the remaining no-pack and generic fallbacks, `scannerDrop`, universal
`scan_trace`, and corrected Group 7.7 remain open. Actual directed counts must
be remeasured; source edits alone do not warrant this prediction.

First falsifier: compile the restored-cover signatures and preserve all failures.
Then prove the state-membership fact, consume it at the three fallback callers,
compile the capstones, re-run owner censuses, and compare exact axiom profiles.
