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

## Continuation: native explicit-content consumer

Decision remains **UNKNOWN for global hRoute**. Separate branch
`research/directive-paired-content` starts at exact
`7d3d21ea06ba849ae07180b65097366fe04b5cc4`, tree
`bc42af6f2c9109935a42d8513a79efbaecc7b376`. That parent's
[Actions #44698726735](https://github.com/metalogiclabs/L4YAML/actions/runs/44698726735)
is now **SUCCESS**. Run and job metadata were read back: targeted proofs,
default build, both hygiene gates and the protected executable all succeeded;
job completion is `2026-11-20T08:23:36Z`. Upstream main, owner integration and
PR #359 were re-read and still match the three exact heads above. No concurrent
branch was overwritten.

The next experiment named above is now paid:

- `RightWallContent.content_step_routed0` generalizes the existing verified
  content worker to keep a nonempty open-event prefix and distinguish the
  closed boundary from the current node's start.
- `content_after_docStart` derives that worker's route from the actual native
  document-start marker and the preceding annotated stream. Plain, quoted,
  block-scalar, property and alias arms reuse the existing leaf proofs.
- `directive_after_pending_document` consumes the resulting matched pending
  state, closes it through the actual preprocessing/comments, scans `...`,
  preserves the full event fold through the next preprocessing and supplies
  the lawful suffix route at the existing `directive_step_noPending` caller.
  An event-prefix equality or `hRoute` is not an input to this consumer.
- `RightWallContentNative.native_directive_after_explicit_scalar` is a
  **closed, assumption-free instance** for
  `---\nx\n...\n%YAML 1.2\n---\ny`: it constructs the real scanner seed,
  checks all four `scanNextToken` edges, derives `ContentArm` from the actual
  content dispatcher, and uses these producers and consumer to obtain the
  annotated stream, pending directive state and explicit `DirectiveRoute`
  certificate with the exact closed events `[beginDocument, endDocument]`.
  Captured intermediate states are checked by kernel reduction against native
  transitions; they are not assumed reachable. No new `native_decide` call is
  used for these transitions.

The three generic lemmas still have their declared local source/trace
premises. The closed native instance discharges those premises for one real
execution, not every execution. The experimental producer is imported by its
explicit proof targets; the public serialization umbrella and the global
scanner induction are unchanged. This is not closure of the mission's
universal caller.

Validation on this continuation: the explicit proof/probe/axiom target builds
**156/156 jobs**, exit 0; repository default `lake build` **1,573/1,573 jobs**,
exit 0; unchanged protected executable **62,260/62,260 assertions**, exit 0.
The protected blob and SHA256 above, toolchain and dependency manifest are
unchanged. The keyword gate still checks 26 sites and the original strict
serialization sweep still observes all 61 profiles with its negative control.
No census pins were changed in this continuation.

The new content proofs reuse scalar/property source proofs whose reflected
axioms already exist at the parent. They are not standard-three-only proofs:
the worker and document-start producer each inherit 28 axioms (standard three
plus 25 existing reflected leaves); the native witness inherits 41 (standard
three plus 38 existing reflected leaves). The document-end/directive consumer
uses only the standard three. `RightWallContentAxioms` checks the actual
transitive axiom sets against the unchanged parent content producer and source
dispatcher, rejects `sorryAx` and any fresh axiom, and prints the profiles.
The strict serialization headline sweep was not relaxed; these additional
profiles are explicitly checked in the new test target.

Seven positive native event probes cover plain/inline/quoted/block scalar,
anchor and named-tag paths. Fourteen candidate malformed-prefix
counterexamples (extra nodes, repeated commas, duplicate properties, orphan
directives and repeated colons) are refused by the actual scanner. Fuel
0/1/2 controls remain. These probes are not grammar non-membership proofs and
did not refute the global invariant. Failed proof attempts involved scope,
record layout and elaboration cost. Nested executable state definitions and
implicit source-position inference caused heartbeat exhaustion; explicit
captured states, native edge equations and named source indices compile.
None of these failures is recorded as a reachable mathematical counterexample.

The **global residual type above is unchanged**. Missing paired producers
include property-run continuation, indented block/map values and base-flow
return to the stream. At a base flow close,
`ContentBridge.accum_step_flow_pairK` yields annotated `TFlowContent` and
source-side `PendingNode`, but not the matching `TPendingNode`/T stream route.
Its source return passes through `pendingFlow`/`scannerDrop`; there is no
permitted automatic conversion of that S route into a T route.

The smallest consequential next experiment is the genuine root-flow path
`[a]\n...\n%YAML 1.2\n---\ny`: produce the paired return certificate from
the real base opener and consume it at the base closer and next directive,
without adding an unproved T-resume premise. Generalizing that certificate
must fund every relevant block/flow producer in the actual global induction.
S3, S4/coherence, Row 12, exact surface correspondence and the scanner/parser
converses remain separate Group 7.7 obligations.

## Base-flow source-origin interface audit

Separate `research/directive-flow-origin` starts at exact `80a0536c45d27fe711818eff60c7a45244faf09b`.
No production grammar, scanner transition or invariant is changed by this audit.

`TFlowOpenStack.seqBase` / `mapBase` deliberately keep the outer boundary
separate from the opening bracket. Their documentation explicitly omits the
enclosing source stack's `resume`, `promise` and `inject` evidence. The existing
T frame algebra and `TSeqFrame.closeBase` are reused unchanged.

`Tests/Guards/Proofs/RightWallFlowOrigin.lean` proves, for every character
suffix, that an empty flow base can have either of two distinct opening
positions while fitting the same exposed T-stack indices and empty event
list. The shared closing literal yields T flow content at either origin.
`base_origin_uniqueness_refuted` rejects the precise interface claim that the
optional separation and current cursor uniquely determine the opener.

Native controls use ` [ ]\n...\n%YAML 1.2\n---\ny`: real preprocessing reports
the opening bracket at offset/column 1 and the closer at offset/column 3;
the complete native scan accepts and emits the expected document events.
Fuel 0/1/2 controls refuse completion. The native control and the abstract
interface refutation have different verification boundaries.

This is **not** a pair of scanner-reachable histories with contradictory
routes, a counterexample to global hRoute, or proof that no stronger existing
native evidence can recover the binding. It establishes that the required
source-origin identity must not be inferred from these exposed indices alone.
The next consumer must either derive that identity from actual opener evidence
or preserve an explicitly source-bound T return obligation. Its native
construction and preservation remain unpaid; no speculative carrier is added.

The existing `FlowArm.openBase.h_sp` already supplies its stated landing
equality on this tree (item 520). The old census's `broken` label is not
evidence that this paid equality is still missing. Source/T-origin binding and
the T return into the enclosing stream are separate obligations.

The narrow Lean 4.35.0 audit passes 149/149 jobs. The two origin statements use
`propext`/`Quot.sound`; the existing-close composition uses the standard three.
There is no `sorryAx`, custom axiom or new reflected leaf. All protected cases
and production sources are unchanged. Default build: 1,573/1,573 jobs;
protected executable: 62,260/62,260 checks; keyword gate: 26 sites;
strict serialization hygiene: 61 profiles. Global hRoute remains UNKNOWN.

## Funded base-flow return and native consumer

`research/directive-flow-return` starts at exact published origin-audit commit
`29d1589bf85d210bd1a33190a8d2118723fbe915`, tree
`fc3b2c3ad2378b2f1a98e47199f51d109d01cf6d`. The parent audit now has a successful
hosted run: https://github.com/metalogiclabs/L4YAML/actions/runs/44707781956.
Upstream main was rechecked as `122064d0c853be8d6c2f4cd255c6fcd67acc4ae8`;
PR 359 remains open at `57721b243c6f1bdd33e8d49c9aedd4f15e552c58`.
This is a separate research line; no concurrent branch or upstream PR is edited.

### Warranted boundary

`TraceOf/FlowReturn.lean` carries an enclosing return obligation at the actual
base opening literal, next to the existing `TSeqFrame` / `TMapFrame`. The
nested frames retain that same obligation. The 26 existing frame-operation
proofs are adapted to this carrier while reusing the original frame algebra.
The native flow-indicator proof retains the key-map effect and the next-colon
continuation, including held properties and nested closes. The content,
property and key arm proofs, and actual preprocessing/content dispatch, also
preserve it. Their premises remain explicit; they do not create an enclosing
return out of an arbitrary source-only route.

`return_first` funds the base return from the real first-document source
prefix and separation. `return_explicit` funds it from the preceding annotated
stream and actual `---` grammar evidence. `returned_pending` spends the return
at the existing `TPendingNode.pendingContent` constructor, preserving the real
node endpoint. At base close the returned endpoint is the closing literal's
endpoint, rather than the source invariant's separate block boundary.

`Tests/Guards/Proofs/FlowReturnNative.lean` proves the closed native path
`[a]\n...\n%YAML 1.2\n---\ny`. It constructs the return at the real opener,
reads the actual content dispatch into the stronger carrier, consumes the
native closer, obtains the matching T pending state, and calls the existing
`directive_after_pending_document` consumer. That consumer supplies `hRoute`
at `directive_step_noPending`. All five `scanNextToken` edges and captured
native states are kernel checked. The final conclusion includes native
`ScannerReachable`, scanner/source correspondence, annotated stream and
pending state with the actual event prefix, and `DirectiveRoute`. It has no
route or return hypothesis. This is a closed instance, not the universal
scanner induction.

The 20 positive native event controls include empty/singleton/nested sequence
and map bodies, explicit keys, JSON-style pairs, trailing commas, properties,
aliases, explicit documents and the next implicit-map-value case `a: [b]`.
Fuel 0/1/2 controls remain. Protected adversarial cases are unchanged.

### Verification and failures

Lean is the repository-pinned 4.35.0, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

- Explicit new proof/control/axiom targets: 158/158 jobs.
- Default `lake build`: 1,573/1,573 jobs.
- Unchanged `lake exe adversarialinstantiation`: 62,260/62,260 checks.
- Keyword gate: 26 whitelisted capstones.
- Strict serialization hygiene: 61 observed profiles, exact headline sets.
- New axiom guard inspects 40 return proof declarations, including an auxiliary
  proof; it hard-fails on coverage drift, `sorryAx` or any dependency outside
  the unchanged original source/content producers' axiom sets. The structural
  return/flow/key lemmas are standard-only. The closed native witness has 41
  inherited dependencies (the standard three plus 38 pre-existing reflected
  leaves); no new reflected leaf or custom axiom is introduced.

The default build alone does not compile the experimental module: the workflow
now explicitly builds its native control and axiom targets. No proof census,
protected case, toolchain pin, source grammar or scanner implementation is
changed in this phase.

Compiler failures were corrected rather than promoted: base-close dependent
elimination over fixed array literals required general kind indices;
reserved identifiers and missing namespace opens caused elaboration errors;
computed scanner-state definitions did not reduce adequately during type
inference, so independently checked captured states are used; floor/position
arguments must be named before checking arithmetic premises. An initial
axiom enumeration using `ConstantInfo.isTheorem` observed zero imported
proofs under Lean's module system. It was rejected and replaced with
`Lean.wasOriginallyTheorem` plus an exact nonzero coverage gate. These are
implementation failures, not reachable counterexamples.

### Global result: UNKNOWN

The actual global `ScannerReachable → DirectiveRoute` theorem is still not
present. The stronger carrier's enclosing return must be created at every
native base-flow birth and coupled with the maintained S pending/block state
and full `goOut` split. The current paid first-document and explicit-document
routes do not discharge all block-context births. In particular, a successful
implicit-key `:` transition needs the T sibling of the source
`ImplicitKeyPack` mapping-entry route, then a matching
`TPendingNode.pendingMapValue` whose closure funds the subsequent flow opener.
The current content pending constructor retains a stream-closing continuation;
it does not itself supply this mapping-entry continuation.

The unpaid return at an actual base opener has type, with the enclosing event
prefix fixed by the native `goOut` invariant:

```lean
∀ finish events, TFlowContent n .flowOut root finish events →
  ∀ mid, SSLComments finish mid →
    TLYamlStream start mid (prior ++ events)
```

The source-only `FlowBaseRoutes.value` proves the S sibling, not this type.
The paired implicit-key producer must additionally retain a T implicit key
and a source-bound mapping-entry continuation of the form:

```lean
∀ stop events, TBlockMapEntry k keyStart stop events →
  TLYamlStream start stop (closedEvents ++ precedingOpenEvents ++ events)
```

These obligations originate in the native block-indicator transition and its
source `ImplicitKeyPack`/pending-map return; they are not replaced by a new
free `hRoute` or assumed global return. The source `pendingFlow` /
`SLYamlStream.scannerDrop` escape still gives no automatic T conversion.
No actual reachable refutation of global hRoute was found.

The smallest consequential next experiment is the **paired native implicit
mapping producer** on `a: [b]\n...\n%YAML 1.2\n---\ny`: preserve the key's
T derivation and enclosing mapping-entry route through the successful `:`,
construct the real pending-map-value closure, use it to fund the flow return,
and consume the next directive. Its native event control already passes.
Then all corresponding native producer cases must pay the same invariant;
more example counts do not discharge that universal obligation.

Remaining Group 7.7 work includes the other S3 producers, the global paired
scanner induction, `scannerDrop`/Row 12, S4/coherence, exact surface
correspondence, and the scanner/parser converse obligations. Neither this
closed path nor a green adversarial run establishes Group 7.7 completion.
