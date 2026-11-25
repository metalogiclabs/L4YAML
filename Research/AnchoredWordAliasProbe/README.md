# Later-alias causal probe

Bounded native result on exact owner
`0dbf0c120601fccc1d837025f3bef405cc4f2062`, Lean 4.36.0. This is the next
experiment after the anchored-word proof at
`83a6e3e2bd6a47768aaaba427838dce53057f8f3`; it is not an unbounded alias proof
and is not included in that proof's hosted qualification.

Source: `? key\n: &a value\n? copy\n: *a`.

All 697 executed cases passed exact raw and composed payload checks and the
ordered event check `[defineAnchor "a", useAlias "a"]`. The set is all 676
single lowercase-letter key/value pairs plus 21 length pairs, with key lengths
1, 2, 31, 1023, 1024, 1025, 2048 and value lengths 1, 1025, 2048.

For each case, `reachAlias` starts from the actual initialized scanner and
executes its transitions to the alias. The reached registry is exactly
`#["a"]`; consuming the alias succeeds and reaches EOF. At that same point:

| Intervention | Observed result |
| --- | --- |
| Delete registry | 697/697 reject with `undefinedAlias "a"` |
| Rename registry to `#["b"]` | 697/697 reject with `undefinedAlias "a"` |
| Restore `#["a"]` | 697/697 consume successfully |

The altered states are intentional causal interventions. No claim is made
that those altered states are independently reachable from the same source.
The positive route is actual native initialization; scanner acceptance and
round-trip agreement alone are not the payload oracle.

The unbounded source-family theorem remains CANDIDATE, not WARRANTED. The
smallest next proof extension is to generalize the existing word stopping
lemma to the under-indented `? copy` line and compose the second actual entry
and alias transition while retaining the first entry's registry. Full
`scan_trace` and Group 7.7 remain open.
