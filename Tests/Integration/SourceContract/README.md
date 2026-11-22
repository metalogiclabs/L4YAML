# Source-contract replay

These five Lean files are unchanged copies from
[metalogiclabs/L4YAML@bf6563fb22f2d140633468884f380304129c9ddb](https://github.com/metalogiclabs/L4YAML/tree/bf6563fb22f2d140633468884f380304129c9ddb/Tests/Guards/Proofs).
`SHA256SUMS` binds their bytes; verify it from this directory with
`sha256sum -c SHA256SUMS`.

Source ancestry: owner base `14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f` →
`cbc2ca9d963f6bc065f30b4ba122884fa4e27cf5` →
`bf6563fb22f2d140633468884f380304129c9ddb`. The latter two commits add only tests,
workflows, and reports. Their production `L4YAML` subtree is unchanged:
`4197c0b6f2fb369e9806ca486d38aef87b077c81`.

The frozen-source comments inside the files are historical. The combined
PR #302/#361 qualification replays these unchanged proofs against its own
production tree. Only a successful new run, recording the combined commit,
tree, toolchain, and these checksums, binds the conclusions to that tree.

| Probe | Exact boundary |
| --- | --- |
| `UpstreamForwardCounterexample` | Four bytes `61 0a 2a 78` (`a\n*x`): parser acceptance, an ill-formed alias trace, and refutation of the fixed original forward contract/biconditional. |
| `UpstreamColonTrace` | Seven bytes `3f 20 2d 0a 20 20 3a` (`? -\n  :`): **positive** two-bare-document trace under the original broad continuation grammar. |
| `UpstreamScannerTrace` | Actual scanner events are `[]`; the exact original scanner-to-trace instance holds. |
| `UpstreamColonRuntime` | Scanner acceptance and token-parser rejection for the same seven bytes. |
| `AcceptedTraceContract` | Conditional interface lemmas through the real production consumers. They do not supply trace, coherence, or reverse-certificate producers. The four-byte refutation rules out globally supplying the full forward premise package for the unchanged `TraceWellFormed` relation. |

The workflow compiles these files explicitly with this directory as Lean's
`--root`, a fresh output directory on `LEAN_PATH`, and
`UpstreamColonTrace` first. Original module names/imports stay intact.
No default test/census root imports this replay directory. Its 21 named
`#print axioms` sites must all appear and use only `propext`,
`Classical.choice`, `Quot.sound`, or no axioms.

Original-source CI: [44802246817](https://github.com/metalogiclabs/L4YAML/actions/runs/44802246817)
covers alias/scanner/colon derivation at `bf6563fb22f2d140633468884f380304129c9ddb`;
[44801221271](https://github.com/metalogiclabs/L4YAML/actions/runs/44801221271)
covers colon/native/conditional consumer at `cbc2ca9d`.

These conditional lemmas are not a viable closure plan for the unchanged
`TraceWellFormed` relation. This replay does not close Group 7.7, `scan_trace`,
or the exact source-language contract. The corrected-research grammar's colon nonmembership and the old
duplicate-TAG acceptance proofs concern other source versions and are absent.
PR #361 supplies the current TAG rejection and completeness-consumer guards.
