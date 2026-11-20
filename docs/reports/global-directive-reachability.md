# Global directive-route reachability campaign

Decision: **UNKNOWN for global hRoute**. This tree does not declare a completed
`scan_trace` or Group 7.7 theorem. No reachable counterexample was found.

## Source and lineage

The separate `research/global-directive-reachability` branch starts at
`0629c30312de09805c70634ae9f3625c0572a16d`, not at a moving integration branch.
The upstream heads inspected were:

| Ref | Exact commit |
| --- | --- |
| NASA/JPL main | `122064d0c853be8d6c2f4cd255c6fcd67acc4ae8` |
| fix-a-grammar-completeness | `b9e0a5b52f8731afbe603b4ae0f32df438073319` |
| PR #359 | `57721b243c6f1bdd33e8d49c9aedd4f15e552c58` |

The five reference runs were read back through GitHub. Each reports SUCCESS at
its declared exact source SHA:

| Source | Run | Verification boundary |
| --- | --- | --- |
| `ba12de17ff1339b6711fddd15f27b183d3ab7509` | [44674504472](https://github.com/metalogiclabs/L4YAML/actions/runs/44674504472) | Lawful directive-state integration, protected adversarial checks |
| `0629c30312de09805c70634ae9f3625c0572a16d` | [44687031951](https://github.com/metalogiclabs/L4YAML/actions/runs/44687031951) | Native seed and source/event consumers, protected adversarial checks |
| `09eeb316225759a67aad88aec59fbabd5eac38b7` | [44689604419](https://github.com/metalogiclabs/L4YAML/actions/runs/44689604419) | Successful directive history preservation |
| `ea3fc8626ceb3d4f7b7326978898d30d520b0ddf` | [44683187977](https://github.com/metalogiclabs/L4YAML/actions/runs/44683187977) | Token-history algebra and native document-end producer |
| `c311255f960d715da5dcbef0a3fc7bb8c6cc7f58` | [44678933154](https://github.com/metalogiclabs/L4YAML/actions/runs/44678933154) | Conditional S/T admission cut |

The token-history and directive-step files are reused from the two corresponding
reference trees. Their proof bodies are retained; the copied directive theorem
uses `lemma` to follow the repository keyword rule. The conditional admission
cut is not imported as a substitute for its missing premises.

## What this tree proves

1. `RightWallHistory.ScannerReachable` contains the genuine BOM-aware scanner
   seed and **every** successful `scanNextToken` successor, with no history,
   grammar, route, successful-final-scan or acceptance premise in its
   constructors. `reachable_history` proves that all such states with
   `allowDirectives = true` satisfy `EligibleHistory`. Preprocessing, directive
   transitions, document ends, document starts and every content fallthrough
   are accounted for. Ordinary branches are handled by the actual flag clear.
2. Source-side `PendingNode.noPending` now carries the real scanner-token
   projection at a virgin block-context park. All nine native construction
   sites are paid: the real seed produces only `streamStart`; the other eight
   sites are flow-interior cases. This strengthens the internal `PendingNode`
   premise; every native producer discharges its new field. The successful-scan
   entry statement retains its original input-level hypotheses and compiles
   through `scanNextToken_accum_step` and `scanLoop_grammar_prod`.
3. `preprocess_goOut` proves full equality of the native event fold, including
   pending tag handles, across preprocessing.
4. `directive_step_source_noPending`, consumed by
   `RightWallBoundary.first_directive_from_source_park`, constructs the first
   annotated stream and its route from the S-side park. It assumes neither
   `hRoute`, event emptiness, a source-prefix witness, nor a previous T stream.
5. `docEnd_step_from_pending` closes an already matched T pending document,
   transports its events through real preprocessing and scans the actual
   document-end marker. The old-token prefix equality and the open
   `[endDocument]` event are conclusions of this transition. Existing lawful
   suffix-route and continuing-directive consumers remain available.

The measured Row 12 park-dependency bill increases: direct users 11 → 12,
transitive dependents 40 → 42. The new source projection and its T consumer are
explicitly counted. This is not a claim of reduced Row 12 work or net global
closure.

Items 1 and 2 are universal native invariant work, not further conditional
route algebra. Item 5 remains a transition from an existing matched T state;
this report does not claim that state exists at every reachable input prefix.

## Exact remaining obligation

At an arbitrary reachable successful document-end dispatch, with the actual
preprocessed scanner `prep` coupled to `markerStart`, establish:

```lean
∃ ev : List Event,
  TSLYamlStream ⟨input.toList, 0⟩ prep markerStart ev [] []
```

The hypotheses must be the real scanner prefix, preprocessing, successful
validation gates, source correspondence and successful marker transition.
A previous annotated stream, a route, an event-prefix equality or a matched
T pending state must not be added as an unproved hypothesis of the global
statement. The existing `docEnd_step_from_pending` consumes such a matched
state locally; the missing global producer is the paired S/T accumulation
through the preceding document's content and block/flow structure.

The current StreamBridge has local constructors and steps, but no global
`scanLoop_trace` induction. Merely obtaining an `EligibleHistory` token split
cannot establish `TLYamlStream` for the earlier source or identify that
split's event prefix with its closed trace. `DirectiveRoute` explicitly
requires that earlier annotated grammar witness in its suffix alternative.

The unpaid S3 roster is recorded in DOCS item 529: the remaining
`accum_content_pending` parks, indented map-value/block content producers and
the base-flow close producers. The flow cases remain tied to Row 12's
`PendingNode.pendingFlow` / `SLYamlStream.scannerDrop` redesign. Source-side
`scanLoop_grammar_prod` is not a T trace proof.

The smallest next consumer experiment is the T producer at `pendingDocStart`,
consumed immediately by `docEnd_step_from_pending` on
`---\nx\n...\n%YAML 1.2\n---\ny`. Then use a completed-flow predecessor such as
`[a]\n...\n%YAML 1.2\n---\ny` to expose the Row 12 dependency. Neither bounded
case alone would establish the universal theorem.

## Validation and negative lineage

Toolchain is the unchanged repository pin, Lean 4.35.0 (commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). The protected adversarial source,
Lean toolchain and dependency manifest remain unchanged from `0629c303`.

The serialization checker initially failed because it copied unqualified print
names into a probe that imported only the umbrella module. Print sites are now
fully qualified and the checker builds/imports their defining modules. Its
negative control and all 61 observed profiles pass; the theorem-keyword gate
passes all 26 whitelisted capstone sites. No axiom check was removed.

The first full default build found two constructor-shape guard updates required
by the new source field, measured census changes, and two old ambiguity witnesses
that relied on the superseded annotated `implicitContinue` rule. Those negative
witnesses are retained against an explicitly named, test-only `LegacyStream`;
the corrected-grammar positive witnesses remain typed as `TraceOf`. Production
grammar was not relaxed to make the tests pass. Local elaboration corrections
were syntax, simplification and case-dispatch errors, not counterexamples to
the native invariant.

The final full default `lake build` passed **1,573/1,573 jobs**, exit 0.
The integrated targeted build passed 157/157 jobs. The unchanged protected
executable passed 62,260/62,260 assertions. The new proof declarations report
only `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`; the
existing source-loop proof retains its pre-existing reflected `native_decide`
leaves.

Final default-build results and exact source/run identities are recorded in the
branch's Actions run and the ROS SYNTHESIS entry. The workflow prints both commit
and tree identity and explicitly builds the new proof module before the default
build and protected adversarial run. A green run certifies these statements and
tests, not global hRoute, S3, S4, Group 7.7, or complete YAML conformance.

Beyond global S3, Row 12 removal of `scannerDrop`, S4 uniqueness or a sufficient
property-relative alternative, the exact surface language and scanner/parser
converses remain separate Group 7.7 obligations. No upstream merge, PR #302 edit
or collaborator contact is part of this campaign.
