import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flip's remainder, mapped (DOCS items 171–175)

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

/-! …and the INDICATOR-headed siblings — the `:`/`?` opened at a still-open
level's own width, which is what item 173's resume arm at
`colon_open_map`/`question_open_map` serves.  One mapping each, the empty or
explicit key consed as the level's next entry — at the root, one level in,
and on the awaited-value park (`k:⏎: 2` = `{k: null, null: 2}`, the flow twin
of which is §5's `k:⏎[1]: b`).  References: the SUITE certifies the colon
family itself — 2JQS is `: a⏎: b` with exactly this one-mapping event list —
and `[192]`'s `e-node` key alternative is the production; PyYAML is NOT the
reference here (it refuses every empty implicit key, first entry included —
its known `[192]` gap), while it parses the `?` siblings with matching
events.  The dedent-crossing colon sibling (`a:⏎- x⏎: 2`) is the same
reading at the parser and the swap's RECORDED residue on the proof side: the
entry parks carry no mapping-lane frames, so that landing keeps the guarded
fallback until a carrier crosses the `-`'s close. -/
#guard pins ": 1\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL : =VAL :1 =VAL : =VAL :2 -MAP -DOC -STR")
#guard pins "a: 1\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 =VAL : =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  a: 1\n  : 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 =VAL : =VAL :2 -MAP -MAP -DOC -STR")
#guard pins "k:\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : =VAL : =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n? b\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  ? a\n  : 1\n  ? b\n  : 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP -MAP -DOC -STR")
#guard pins "a:\n- x\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a +SEQ =VAL :x -SEQ =VAL : =VAL :2 -MAP -DOC -STR")

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

/-! ## §3b  Items 174–175 — the props ride across the break

`[161] ns-flow-node`'s third alternative separates the properties from the
content with `s-separate(n,c)`, which is `s-separate-lines` in every non-key
context — the BREAK IS INSIDE THE NODE.  So a sentinel-level `[96]` park's
break-crossed content is the run's OWN node, not an anchored-empty document
followed by a bare second one: the scalar and quoted forms ride `[161]`'s
props alternative, the block scalar rides `[198]`'s slot, and the implicit-key
mapping rides `[196] s-l+block-collection`'s optional properties — the
MAPPING's anchor (`+MAP &p`), where the same-line `&p b: 1` anchors the KEY
(`+MAP =VAL &p :b` — PyYAML agrees on both readings).  The ride bottoms in
the park's own route, so the seed, the marker and the suffix parks all ride
identically, and the explicit value's park (`? k⏎: &p⏎b` = `{k: &p b}`) is
the same `n = 0` swap — there PyYAML refuses at its simple-key scanner, a
PyYAML-side gap like `[192]`'s.

Item 174 paid the CONTENT-dispatch rides at the sentinel-indexed park.
**Item 175 paid the INDICATOR-dispatch rides**: a landed `-`/`?`/`:` opens
the RUN's own collection — `[196]`'s optional properties again, the
COLLECTION's anchor (`&p⏎- a` = `+SEQ &p`, where the same-line `&p - a` is
scanner-refused; `&p⏎? x⏎: v` and `&p⏎: v` = `+MAP &p`) — through the same
park route, carried as `PropsNodeRoute` (the ride's landing half): the FIFTH
arm of the `:`/`?` openers' cascades and the `-` arm's entries route
(`propsSeqRoute`).  PyYAML agrees on every accepted family below except its
three known gaps: the empty implicit key (`&p⏎: v` — `[192]`, the suite's
2JQS lineage is the reference), the explicit value's simple key
(`? k⏎: &p⏎…`), and ANY bare document after a `...` suffix (it refuses the
anchor-free `a: 1⏎...⏎b: 2` identically — `[210]`'s
`l-document-suffix+ l-any-document?` is the reference).

**Item 175 also STRUCK one of item 174's punt rows**: the flow-open ride
(`&p⏎[1, 2]`) was never on the fallback — `accum_flow_open_depth0`'s
`pendingProps` arm has ridden the run into the flow node (break or not,
`SFlowNode.propsContent` through the park's route) since items 9h/12, and
its only other branch serves under-run parks, which cannot exist at `n = 0`.

Recorded punts, each with the fallback still standing: the ENCLOSING-level
indented rides (`k:⏎  a: &p⏎    c: d`, `k:⏎  a: &p⏎  - w` — the ride pays
`n = 0` only), the two-park chain (`!t⏎&q b` and its break variants — one
`[96]` run whose internal separate crossed the break; the run-extension arm
is the NO-BREAK branch's, measured at item 175), the enclosing park's col-0
sibling `:` (`k:⏎  a: &p⏎: v` — a `[96]` park carries no mapping-lane
frames, item 173's recorded residue), and the alias landing (`&p⏎*p`,
scan-accepted and parser-refused).  The enclosing-level park's dedented
landing keeps `propsEmpty` + the sibling resume — the honest reading there
(`k:⏎  a: &p⏎c: 2`, `k:⏎  a: &p⏎  c: d`). -/

-- the paid rides: scalar, comments interleaved, indented, quoted, block
-- scalar, tag, two-half run, and the implicit-key mapping (root + indented)
#guard pins "&p\nb\n" == ("scan-accepted", "+STR +DOC =VAL &p :b -DOC -STR")
#guard pins "&p\n# c\nb\n" == ("scan-accepted", "+STR +DOC =VAL &p :b -DOC -STR")
#guard pins "&p\n  b\n" == ("scan-accepted", "+STR +DOC =VAL &p :b -DOC -STR")
#guard pins "&p\n\"b\"\n" == ("scan-accepted", "+STR +DOC =VAL &p \"b -DOC -STR")
#guard pins "&p\n|\n  x\n" == ("scan-accepted", "+STR +DOC =VAL &p |x\\n -DOC -STR")
#guard pins "!t\nb\n" == ("scan-accepted", "+STR +DOC =VAL <!t> :b -DOC -STR")
#guard pins "&p !t\nb\n" == ("scan-accepted", "+STR +DOC =VAL &p <!t> :b -DOC -STR")
#guard pins "&p\nb: 1\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :b =VAL :1 -MAP -DOC -STR")
#guard pins "&p\n  b: 1\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :b =VAL :1 -MAP -DOC -STR")
-- …through the marker's, the suffix's and the explicit value's own routes
#guard pins "---\n&p\nb\n" == ("scan-accepted", "+STR +DOC --- =VAL &p :b -DOC -STR")
#guard pins "a: 1\n...\n&p\nb\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC =VAL &p :b -DOC -STR")
#guard pins "? k\n: &p\nb\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &p :b -MAP -DOC -STR")
-- the boundary: the enclosing-level park closes propsEmpty and the landing
-- resumes — the honest reading the ride must NOT displace
#guard pins "k:\n  a: &p\nc: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL &p : -MAP =VAL :c =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  a: &p\n  c: d\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL &p : =VAL :c =VAL :d -MAP -MAP -DOC -STR")
-- item 175's paid rides: the landed `-`/`?`/`:` at the sentinel park opens
-- the run's own collection (multi-entry, indented, comment-interleaved,
-- valueless explicit key, tag, and two-half runs included)
#guard pins "&p\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "&p\n? x\n: v\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :x =VAL :v -MAP -DOC -STR")
#guard pins "&p\n: v\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL : =VAL :v -MAP -DOC -STR")
#guard pins "&p\n- a\n- b\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a =VAL :b -SEQ -DOC -STR")
#guard pins "&p\n  - a\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "&p\n# c\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "&p\n? x\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :x =VAL : -MAP -DOC -STR")
#guard pins "!t\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ <!t> =VAL :a -SEQ -DOC -STR")
#guard pins "&p !t\n? x\n: v\n" == ("scan-accepted", "+STR +DOC +MAP &p <!t> =VAL :x =VAL :v -MAP -DOC -STR")
-- …and through the marker's, the suffix's and the explicit value's routes
#guard pins "---\n&p\n- a\n" == ("scan-accepted", "+STR +DOC --- +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "a: 1\n...\n&p\n- a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "---\n&p\n: v\n" == ("scan-accepted", "+STR +DOC --- +MAP &p =VAL : =VAL :v -MAP -DOC -STR")
#guard pins "? k\n: &p\n- w\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ &p =VAL :w -SEQ -MAP -DOC -STR")
#guard pins "---\n&p\n? x\n: v\n" == ("scan-accepted", "+STR +DOC --- +MAP &p =VAL :x =VAL :v -MAP -DOC -STR")
-- the flow-open ride, paid on the FLOW lane since items 9h/12 (item 174's
-- punt row for it was wrong; struck at item 175)
#guard pins "&p\n[1, 2]\n" == ("scan-accepted", "+STR +DOC +SEQ [] &p =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "---\n&p\n[1]\n" == ("scan-accepted", "+STR +DOC --- +SEQ [] &p =VAL :1 -SEQ -DOC -STR")
-- the recorded punts (all accepted, still on the fallback readings)
#guard pins "k:\n  a: &p\n    c: d\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a +MAP &p =VAL :c =VAL :d -MAP -MAP -MAP -DOC -STR")
#guard pins "k:\n  a: &p\n  - w\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a +SEQ &p =VAL :w -SEQ -MAP -MAP -DOC -STR")
#guard pins "k:\n  a: &p\n: v\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL &p : -MAP =VAL : =VAL :v -MAP -DOC -STR")
#guard pins "!t\n&q b\n" == ("scan-accepted", "+STR +DOC =VAL &q <!t> :b -DOC -STR")
#guard pins "&p\n!t b\n" == ("scan-accepted", "+STR +DOC =VAL &p <!t> :b -DOC -STR")
#guard pins "!t\n&q\nb\n" == ("scan-accepted", "+STR +DOC =VAL &q <!t> :b -DOC -STR")
#guard pins "!t\n&q\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ &q <!t> =VAL :a -SEQ -DOC -STR")
-- the refused shapes beside them
#guard pins "&p\nb\nc: 1\n" == ("scan-refused L4YAML.ScanError.invalidImplicitKey 2", "ERR L4YAML.ScanError.invalidImplicitKey 2")
#guard pins "&p\n&q b\n" == ("scan-accepted", "ERR L4YAML.ScanError.duplicateAnchor 1")
#guard pins "&p\n*p\n" == ("scan-accepted", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  a: &p\n- w\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "? k\n: &p\n[1]\n" == ("scan-EOF-refused L4YAML.ScanError.underIndentedFlowContent 2 0", "ERR L4YAML.ScanError.underIndentedFlowContent 2 0")

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
| `rootMapRoute(F)_or_refused` at `h_op = true` (from `colon_open_map`, `question_open_map`, `content_dispatch_routed` ×2) | §1's sibling keys | the resume routes at the open level's frames — **the two openers CARRY the resume arm as of item 173** (`h_res_land`, first in the cascade) **and the props arm as of item 175** (`h_pr_land`, fifth — the sentinel `[96]` park's landed `:`/`?` heads the RUN's collection), paid by `pendingContent.h_framesS`, `pendingMapValue.h_frames` and `pendingProps.h_route`; what still reaches the guard is a landing whose park pays no face (the dedent-crossing colon sibling `a:⏎- x⏎: 2` and §3b's enclosing-park residues, the recorded ones) |
| `bareNodeRoute_or_refused` at `h_op = true` (from `accum_block_on_closeThenBlock`) | §1's sibling keys and open-sequence entries | same |
| `content_dispatch_after_close` | §1's siblings after an empty close (`k:⏎a: 1`) resume ALREADY (items 109/151 — the entry route threads `resumectx_of_landing` at all three callers, measured at item 174); what the raw route itself still serves is §4's scalar family (`k:⏎a`, its pendingMapValue caller) and §3b's rides | the sibling half is PAID; §4's half is 1d's; ~~the props half~~ **PAID by item 174** (the ride context bypasses the route at the sentinel park) |
| the guards at `Or.inr` (parks with no `CompletedTail`) | §4's family is the scalar half of what reaches them; `bareNodeRoute_or_refused_content`'s two arms' LIVE payers are `pendingFlow`'s break-crossed landings alone (measured at item 174: `pendingContent`/`pendingBlockContent` pay `Or.inl` and refute, the marker parks exit on their own arms) | shrinks with 1d's runtime fix and R3's `pendingFlow` deletion; the sibling residue resumes |
| `accum_content_pending`'s pendingProps landing (via `content_dispatch_after_close`) | §3b's rides — the sentinel run's break-crossed node (`&p⏎b`, `&p⏎b: 1`, `&p⏎|⏎  x`) read as propsEmpty + a bare second document | **PAID by item 174**: `PropsRideRoute` carries the park's route + run, `content_dispatch_routed` assembles `[161]`/`[198]`/`[196]`'s props slots, and the enclosing-level park (`0 < n`) keeps propsEmpty + resume; residues = the indented-enclosing/two-park/alias punts pinned in §3b |
| `accum_block_pending`'s pendingProps landing (via `accum_block_on_closeThenBlock`) | §3b's indicator rides — the sentinel run's break-crossed `-`/`?`/`:` (`&p⏎- a`, `&p⏎? x⏎: v`, `&p⏎: v`) read as propsEmpty + a bare second document | **PAID by item 175**: `PropsNodeRoute` (the ride's landing half) rides the same park route into `[196]`'s slot — `propsSeqRoute` at the `-` arm's entries, `propsMapRoute(F)` as the openers' fifth cascade arm; the flow-open twin was paid on the FLOW lane at items 9h/12 (174's punt row for it struck at 175), and the enclosing-level park (`0 < n`) keeps propsEmpty + resume |
| `topLevelFlowResumeSep_or_refused` fallbacks, `flowKeyRoute_of_root` landing arm | §2's sibling flow keys (item 172's key half) | the key half resumes at the open level; the value half is refused at the gate and the refuted arms cover it |
| ~~`flowKeyRoute_of_root` no-break arm~~ | the seed key (`[1]: b`) | **PAID by item 173**: the no-break arm's premise carries the virgin park's own `h_nodoc` face beside the column, so `nodocMapRoute` is the arm's only route and the raw `rootMapRoute` application is deleted — the census's `rootMapRoute` holder is gone |
| `accum_content_pending`'s crossed arms | NONE accepted (§3) | a scanner-side trailing-props refusal (M4 candidate), or the window face carried to the parser boundary |
| `structural_dispatch_to_pending`, `DocumentProduction.stream_implicit_continue` | n/a — `SLAnyDocument.explicit` wrappers | deleted by the flip itself |
-/

end L4YAML.Tests.Guards.StreamFlipRemainderMap
