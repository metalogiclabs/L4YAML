import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flip's remainder, mapped (DOCS items 171–172)

Row 19's 1c ends by narrowing `[210]`'s slot (`GOpt SLAnyDocument` →
`GOpt SLExplicitDocument`), and the narrowing instrument breaks FIVE
definitions: `topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`,
`bareNodeRoute` — the four raw routes that append a completed construct to the
stream as a fresh BARE document — and `structural_dispatch_to_pending`, whose
breaking site passes `SLAnyDocument.explicit` and is the wrapper the flip
itself deletes.  Every consumer arm that still reaches a raw route is one of:

* the four guards' own fallback arms (`*_or_refused` at `Or.inr` and at a
  landing resting ON an open level),
* `flowKeyRoute_of_root`'s no-break arm,
* `content_dispatch_after_close`'s route,
* `accum_content_pending`'s two crossed-window arms (item 170's), and
* `bareNodeRoute_or_refused_content`'s two fallback arms.

This file pins the INPUT families those arms serve, at the runtime, one
`#guard` per family — so the map is measured, and any runtime move flips it
loudly.  Item 171 measured the map and named two findings; item 172 closed the
second, and the pins below are the map at the CLOSED state:

**The value that lands at its own level's column (§4) is an over-acceptance,
and it is 1d's runtime face.**  A scalar landing at exactly the column of the
level whose value is awaited is read as that value (`k:⏎a` = `{k: a}`, plain,
quoted, and block forms, at any depth, in implicit and explicit entries
alike).  `[201] seq-spaces` exempts only the sequence (`k:⏎- a` is the spec's
own), and the scalar forms need `s-separate(n+1)`'s line-crossing branch,
whose `s-flow-line-prefix(n+1)` demands `s-indent(n+1)` — column `n` fails it.
PyYAML (6.x, `yaml.parse`, event level) refuses the plain and quoted forms at
its scanner ("could not find expected ':'") and accepts the block-scalar
header form; no yaml-test-suite case covers any of them.  This is the same
`m = 0` the encoding admits at `SBlockNode.blockSeq`/`blockMap` (item 107,
`BlockCollectionWidthFloor.lean`): the runtime and the grammar over-approximate
TOGETHER, which is why the matrix cannot see either half.  The FLOW half of
this floor is NOT part of the finding: a flow node standing in the awaited
slot at column `n` is refused (`underIndentedFlowContent`, §5) — the scalar
faces alone move with 1d's re-indexing.

**The sibling implicit flow key (§5) is item 172's fix.**  `c-s-implicit-json-key`
is `c-flow-json-node(n/a, block-key)` — the flow key carries no indent
parameter — so a `[`/`{` landing AT an open level's column may be the level's
next KEY, and key-vs-value is not decidable at the open (item 159's own
measurement: a collection can head a key).  §8.1's floor is therefore read at
the CLOSE (`underIndentedFlowValuePos?`, the slot-offered complement of
`danglingNodePos?`): the same-line `:` after the close resolves the key half
through the simple key the close restores — the sibling entry, `a: 1⏎[1]: b`
= `{a: 1, [1]: b}`, exactly the reading the anchor-shifted twin
`a: 1⏎&p [b]: c` has always had — and a landing no `:` resolves refuses at
the break or EOF gate: as the awaited value's own under-indent where the slot
holder OFFERS a node (`k:⏎[1, 2]`, `underIndentedFlowContent` at the open's
position), and as §9.2's dangling node where it COMPLETES one (`a: 1⏎[1, 2]`,
`invalidBareDocument` — the same constructor the scalar twin `a: 1⏎b` gets,
and the same one the anchored twin `a: 1⏎&p [1, 2]` has always gotten). -/

namespace L4YAML.Tests.Guards.StreamFlipRemainderMap

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-- The scanner's own verdict, with `scanLoop`'s EOF checks applied — so a
    refusal names which scanner mechanism produced it, and `scan-accepted`
    means the per-step and BOTH EOF checks passed. -/
private def scanPhase (input : String) : String :=
  let rec go (s : ScannerState) (fuel : Nat) : String :=
    match fuel with
    | 0 => "fuel"
    | fuel' + 1 =>
      match scanNextToken s with
      | .ok (some s') => go s' fuel'
      | .ok none =>
        match scanLoop_checkDanglingNode s with
        | .error e => s!"scan-EOF-refused {repr e}"
        | .ok () =>
          match scanLoop_checkFlowValueIndent s with
          | .ok () => "scan-accepted"
          | .error e => s!"scan-EOF-refused {repr e}"
      | .error e => s!"scan-refused {repr e}"
  go ((ScannerState.mk' input).emit .streamStart) 200

private def flat (s : String) : String :=
  String.intercalate " " ((s.splitOn "\n").filter (· ≠ ""))

/-- Both pipelines' event output, asserted equal — a pin on this is a pin on
    the reading AND on parity. -/
private def evBoth (input : String) : String :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok a, .ok b => if a == b then flat a else s!"MISMATCH {flat a} ≠ {flat b}"
  | .error a, .error b =>
      if reprStr a == reprStr b then s!"ERR {repr a}" else s!"ERR-MISMATCH {repr a} ≠ {repr b}"
  | .ok a, .error b => s!"SPLIT ok {flat a} / err {repr b}"
  | .error a, .ok b => s!"SPLIT err {repr a} / ok {flat b}"

private def pins (input : String) : String × String := (scanPhase input, evBoth input)

/-! ## §1  The block lane: what `bareNodeRoute`'s holders serve

The guards' on-level arms (`rootMapRoute_or_refused`, `rootMapRouteF_or_refused`,
`bareNodeRoute_or_refused` at `h_op = true`, and `content_dispatch_after_close`)
serve exactly the SIBLING landings: a completed entry, a break, the next entry
at the same width.  Every accepted input here is one document read entry by
entry — the resume reading, not a second bare document — which is what the
arms must hand after the flip. -/

#guard pins "a: 1\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "? a\n: 1\n? b\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "[1]: a\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :a =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "k:\na: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : =VAL :a =VAL :1 -MAP -DOC -STR")
#guard pins "k: &p\na: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &p : =VAL :a =VAL :1 -MAP -DOC -STR")
#guard pins "a: |\n  x\nb: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL |x\\n =VAL :b =VAL :1 -MAP -DOC -STR")
#guard pins "a:\n- x\n- y\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a +SEQ =VAL :x =VAL :y -SEQ -MAP -DOC -STR")
#guard pins "k: v\nw: x\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL :v =VAL :w =VAL :x -MAP -DOC -STR")

/-! …and the landings that are NOT siblings are refused by the scanner —
§9.2 at the landing (M1), at EOF (M2), or at the `-` (M3 family) — so the
guards' refuted arms cover them and the raw route serves them nothing. -/
#guard pins "a: 1\nb\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a\n# c\nb\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "\"a\"\nb: 1\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: v\n- a\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")

/-! ## §2  The flow lane after item 172: the key half resumes, the value half
refuses at the gate

`topLevelFlowResumeSep_or_refused`'s fallback arms and `flowKeyRoute_of_root`'s
landing arm serve the deferred floor's two halves.  The KEY half — a landing
flow open whose close a same-line `:` resolves — is the sibling entry, accepted
with the resume reading in both pipelines.  The VALUE half is refused at the
break or EOF gate: `invalidBareDocument` where the run's slot holder completes
a node (§9.2's own reading through the close, item 159's walk-back), and the
more-indented interior refuses by column exactly as before (item 145). -/

#guard pins "a: 1\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n{x: y}: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +MAP {} =VAL :x =VAL :y -MAP =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n[1, 2]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 =VAL :2 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n  a: 1\n  [1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -MAP -DOC -STR")
#guard pins "[1]: a\n[2]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :a +SEQ [] =VAL :2 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "\"x\"\n[1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  \"a\"\n  [1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard pins "k:\n  \"a\"\n    [1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 4", "ERR L4YAML.ScanError.invalidBareDocument 2 4")

/-! The routes the flow lane's park DOES spend — the seed (`nodoc`), the
marker, the suffix — are the flip-legal twins, and their inputs accept. -/
#guard pins "[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "---\n[1]: b\n" == ("scan-accepted", "+STR +DOC --- +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "...\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "&p [1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] &p =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n...\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n...\n[1, 2]\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")

/-! ## §3  The crossed-props arms serve only parser-refused inputs

`accum_content_pending`'s two `PropsWindowCross` fallbacks (item 170) apply the
raw route behind a window premise whose every scanner-reachable input the
parser refuses — `TokenParser.validNextToken`'s own §9.2 reading.  The full
window pins are `PropsCrossWindowRoute.lean`'s; the two families here are the
arms' whole domain. -/

#guard pins "a:\n!t\n&b\n  !s &c x\n" == ("scan-accepted", "ERR L4YAML.ScanError.trailingContent 1 0")
#guard pins "&a\n!t &b x\n" == ("scan-accepted", "ERR L4YAML.ScanError.invalidBareDocument 1 3")

/-! ## §4  Finding A — the value at its own level's column (1d's runtime face)

Six accepted readings the references dispute (PyYAML refuses B1/B2/B6/B7/B9 at
its scanner; the block-scalar header B10 it accepts, and no suite case decides
it), and the boundaries that show the shape: props at the same column are
PARSER-refused, a column BELOW the awaiting level refuses at the scanner, and
the FLOW node at the column is refused by the deferred floor (§5) — the
over-acceptance is the scalar forms' alone. -/

#guard pins "k:\na\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL :a -MAP -DOC -STR")
#guard pins "k:\n\"a\"\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL \"a -MAP -DOC -STR")
#guard pins "k:\n  m:\n  a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :m =VAL :a -MAP -MAP -DOC -STR")
#guard pins "k:\na\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL :a =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "? k\n:\na\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL :a -MAP -DOC -STR")
#guard pins "k:\n|\n x\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL |x\\n -MAP -DOC -STR")
-- the boundaries: properties at the column are refused one stage later, a
-- deeper await is refused at EOF, and the sequence is the spec's own exemption
#guard pins "k:\n&x a\n" == ("scan-accepted", "ERR L4YAML.ScanError.trailingContent 1 0")
#guard pins "k:\n!t a\n" == ("scan-accepted", "ERR L4YAML.ScanError.trailingContent 1 0")
#guard pins "k:\n  m:\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "- k:\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n- a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ =VAL :a -SEQ -MAP -DOC -STR")

/-! ## §5  Item 172 — §8.1's floor at the close

The deferred floor's own boundary map.  The KEY half: a same-line `:` after
the close resolves the collection as the awaiting entry's sibling key — at the
root, one level in, after an explicit entry, and as the awaited value's OWN
sibling (`k:⏎[1]: b` = `{k: null, [1]: b}`, the flow twin of §1's
`k:⏎a: 1`).  The anchor-shifted twin now differs from the bare form by its
anchor alone, in verdict and in events alike.  The VALUE half: an unresolved
slot-OFFERED landing refuses as `underIndentedFlowContent` at the OPEN's own
position (`underIndentedFlowValuePos?` reads the close's matching open,
`flowOpenIdx?`, and the open's column against the open levels — the
`[96]`-transparent slot holder decides offered-vs-completed, so the props face
`k:⏎&p [1, 2]` keeps its Finding-A reading), and a break kills the key exactly
where §7.4's single-line rule says it dies.  The seq sibling refuses at the
resolving `:` (§8.2.1's key-at-sequence-column), the glued `:` at the
adjacent-value check (item 47), and the under-indented INTERIOR line at §8.1's
in-flow check — each the anchored twin's own verdict at the same mechanism. -/

#guard pins "k:\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "? a\n: 1\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n  m:\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :m =VAL : -MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n&p [b]: c\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] &p =VAL :b -SEQ =VAL :c -MAP -DOC -STR")
-- the value half: slot-offered → the deferred floor, at the open's position;
-- slot-completed → §9.2's dangling reading, the anchored twin's constructor
#guard pins "k:\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "a: 1\n&p [1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n&p [b]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n[1]\nb: 2\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n[1]\n: b\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  a: 1\n  [1, 2]\nz: 1\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
-- the twin-consistent refusals at the OTHER mechanisms
#guard pins "- a\n[1]: b\n" == ("scan-refused L4YAML.ScanError.trailingContent 1 0", "ERR L4YAML.ScanError.trailingContent 1 0")
#guard pins "- a\n&p [1]: b\n" == ("scan-refused L4YAML.ScanError.trailingContent 1 0", "ERR L4YAML.ScanError.trailingContent 1 0")
#guard pins "a: 1\n[1]:b\n" == ("scan-refused L4YAML.ScanError.unseparatedValue 1 3", "ERR L4YAML.ScanError.unseparatedValue 1 3")
#guard pins "a: 1\n[1,\n2]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 2 0", "ERR L4YAML.ScanError.underIndentedFlowContent 2 0")
#guard pins "a: 1\n&p [1,\n2]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 2 0", "ERR L4YAML.ScanError.underIndentedFlowContent 2 0")

/-! ## §6  The record

Per surviving arm, what the pins say it serves and what pays after the flip:

| arm | accepted domain (pinned) | post-flip reading |
|---|---|---|
| `rootMapRoute(F)_or_refused` at `h_op = true` (from `colon_open_map`, `question_open_map`, `content_dispatch_routed` ×2) | §1's sibling keys | the resume routes at the open level's frames |
| `bareNodeRoute_or_refused` at `h_op = true` (from `accum_block_on_closeThenBlock`) | §1's sibling keys and open-sequence entries | same |
| `content_dispatch_after_close` | §1's siblings after an empty close (`k:⏎a: 1`) | resume at the level the close kept open |
| the guards at `Or.inr` (parks with no `CompletedTail`) | §4's family is the scalar half of what reaches them | shrinks with 1d's runtime fix; the sibling residue resumes |
| `topLevelFlowResumeSep_or_refused` fallbacks, `flowKeyRoute_of_root` landing arm | §2's sibling flow keys (item 172's key half) | the key half resumes at the open level; the value half is refused at the gate and the refuted arms cover it |
| `flowKeyRoute_of_root` no-break arm | the seed/marker/suffix keys (§2's accepted pins) | the `nodoc`/marker/suffix twins, once the skeleton hands the faces it drops (`accum_flow_open_depth0` passes `Or.inr trivial` for `h_nodoc`) |
| `accum_content_pending`'s crossed arms | NONE accepted (§3) | a scanner-side trailing-props refusal (M4 candidate), or the window face carried to the parser boundary |
| `structural_dispatch_to_pending`, `DocumentProduction.stream_implicit_continue` | n/a — `SLAnyDocument.explicit` wrappers | deleted by the flip itself |
-/

end L4YAML.Tests.Guards.StreamFlipRemainderMap
