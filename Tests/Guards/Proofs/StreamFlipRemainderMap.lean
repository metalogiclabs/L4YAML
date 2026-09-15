import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flip's remainder, mapped (DOCS item 171)

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
loudly.  Two of the families are findings, not fog:

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
TOGETHER, which is why the matrix cannot see either half.

**The sibling implicit flow key (§5) is an over-refusal, and the anchor makes
it an inconsistency.**  `[1]: b` as a mapping's FIRST entry is accepted
(LX3P's own shape), but the same entry as a SIBLING is refused at the flow
open (`a: 1⏎[1]: b` = `underIndentedFlowContent`), because §8.1's floor reads
the bracket's column against the open level before key-vs-value is decidable.
`c-s-implicit-json-key` is `c-flow-json-node(n/a, block-key)` — the flow key
carries no indent parameter — and PyYAML parses all three §5 witnesses at the
event level.  The anchor seals it from inside: `a: 1⏎&p [b]: c` is ACCEPTED,
because `&p` moves the bracket right of the floor — one anchor of width 2
separates accept from refuse on the same grammatical shape.  Item 159 measured
why the open cannot decide this (a collection can head a key), and items
159/161/162 built the close-side reading the deferral needs.

Everything else the arms serve is already sorted by the pins: the block lane's
accepted landings are all SIBLINGS (resume readings — §1), the flow lane's
landings are all refused at today's runtime (§2, empty accepted domain — but
§5 says one of those refusals is wrong, so the lane must not be hardened
against it), and the crossed-props arms serve only parser-refused inputs
(§3). -/

namespace L4YAML.Tests.Guards.StreamFlipRemainderMap

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-- The scanner's own verdict, with `scanLoop`'s EOF check applied — so a
    refusal names which scanner mechanism produced it, and `scan-accepted`
    means BOTH the per-step and the EOF checks passed. -/
private def scanPhase (input : String) : String :=
  let rec go (s : ScannerState) (fuel : Nat) : String :=
    match fuel with
    | 0 => "fuel"
    | fuel' + 1 =>
      match scanNextToken s with
      | .ok (some s') => go s' fuel'
      | .ok none =>
        match scanLoop_checkDanglingNode s with
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

/-! ## §2  The flow lane: every landing is refused at today's runtime

`topLevelFlowResumeSep_or_refused`'s fallback arms and `flowKeyRoute_of_root`'s
landing arm have an EMPTY accepted domain: a depth-0 `[`/`{` reached across a
break from a completed value is refused at or left of the open level by §8.1's
floor (`underIndentedFlowContent`), and everywhere else by §9.2's column
reading (`invalidBareDocument`, item 145) — the more-indented interior
included.  §5 shows one member of the §8.1 family is an over-refusal, so the
lane's arms must not be hardened against these verdicts as they stand. -/

#guard pins "a: 1\n[1]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "a: 1\n{x: y}: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "a: 1\n[1, 2]\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "a: 1\n[1, 2]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "\"x\"\n[1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  \"a\"\n  [1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard pins "k:\n  \"a\"\n    [1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 4", "ERR L4YAML.ScanError.invalidBareDocument 2 4")
#guard pins "k:\n  a: 1\n  [1]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 2 2", "ERR L4YAML.ScanError.underIndentedFlowContent 2 2")

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
it), and the two boundaries that show the shape: props at the same column are
PARSER-refused, and a column BELOW the awaiting level refuses at the scanner. -/

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

/-! ## §5  Finding B — the sibling implicit flow key

Three refusals PyYAML parses at the event level, beside the two acceptances
that frame them: the FIRST-entry flow key (LX3P's shape) and the anchor-shifted
sibling, where `&p `'s two columns are the entire difference between accept and
refuse. -/

#guard pins "[1]: a\n[2]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
-- (the other two sibling witnesses are §2's first two pins)
#guard pins "a: 1\n&p [b]: c\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] &p =VAL :b -SEQ =VAL :c -MAP -DOC -STR")
#guard pins "a: 1\n&p [b]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")

/-! ## §6  The record

Per surviving arm, what the pins say it serves and what pays after the flip:

| arm | accepted domain (pinned) | post-flip reading |
|---|---|---|
| `rootMapRoute(F)_or_refused` at `h_op = true` (from `colon_open_map`, `question_open_map`, `content_dispatch_routed` ×2) | §1's sibling keys | the resume routes at the open level's frames |
| `bareNodeRoute_or_refused` at `h_op = true` (from `accum_block_on_closeThenBlock`) | §1's sibling keys and open-sequence entries | same |
| `content_dispatch_after_close` | §1's siblings after an empty close (`k:⏎a: 1`) | resume at the level the close kept open |
| the guards at `Or.inr` (parks with no `CompletedTail`) | §4's family is the scalar half of what reaches them | shrinks with 1d's runtime fix; the sibling residue resumes |
| `topLevelFlowResumeSep_or_refused` fallbacks, `flowKeyRoute_of_root` landing arm | EMPTY today (§2) — but §5's over-refusal is load-bearing in that emptiness | blocked on Finding B's fix; then the key half resumes, the value half is refused at the close (items 159/161's reading) |
| `flowKeyRoute_of_root` no-break arm | the seed/marker/suffix keys (§2's accepted pins) | the `nodoc`/marker/suffix twins, once the skeleton hands the faces it drops (`accum_flow_open_depth0` passes `Or.inr trivial` for `h_nodoc`) |
| `accum_content_pending`'s crossed arms | NONE accepted (§3) | a scanner-side trailing-props refusal (M4 candidate), or the window face carried to the parser boundary |
| `structural_dispatch_to_pending`, `DocumentProduction.stream_implicit_continue` | n/a — `SLAnyDocument.explicit` wrappers | deleted by the flip itself |
-/

end L4YAML.Tests.Guards.StreamFlipRemainderMap
