import L4YAML.Scanner.Scanner
import L4YAML.Scanner.IndexedDispatch
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The raised-flag refusal map (DOCS item 119)

The tightening's last prerequisite (items 110/116–118) reads: where
`documentEverStarted` is up and no suffix intervened, every input the
fallback `.bare` sites still serve must be scanner-refused.  This item
MEASURED that sentence instead of building on it, and the measurement
repriced it:

**The §9.2 refusal lives in the parser, not the scanner.**  Every family
below scans clean in BOTH pipelines and dies downstream in
`parseStreamLoop` (`StreamState.validNextToken`,
`Parser/TokenParser.lean`) or the emitters' twins — as
`invalidBareDocument`, "expected '---' or '...' before new document".
So the refusal half is a runtime MIGRATION — the scanner must learn the
check — and it decomposes into exactly three mechanisms, each validated
here against the runtime's own verdicts:

* **M1 — the completed root document** (§2): block context, the indent
  stack at its sentinel alone, the last real token a flow close or a
  scalar of any style, and a line break crossed since its end.  Placed
  after the structural dispatch, so `---`/`...`/directives stay legal.
  Same-line junk is already refused (`validateFlowClose`,
  `validateTrailingContent` — §5); a root plain scalar completes only
  where its walk stops (a comment line), and the alias-as-root case is
  unreachable (`undefinedAlias` fires first).
* **M2 — the dangling node run at an open level's column** (§3): a
  trailing token run `[anchor|tag]* (scalar|alias)?` whose start sits at
  an open indent level's exact column, whose structural predecessor is
  NOT `.value`/`.key`/`.blockEntry`, with a break crossed (or EOF, in
  `scanLoop`).  The three exempt predecessors are the equal-column value
  readings the pipeline ACCEPTS — `a:⏎b` = `{a: b}`, `?⏎b⏎: v`,
  `-⏎b` — pinned in §6.
* **M3 — the `-` at a mapping top's own column** (§4): valid iff the
  mapping's value is still awaited (last real token `.value`, or a
  property run after it) or a same-indent sequence is continuing (a
  `.blockEntry` at this column stands before any `.key`/`.value` at a
  column ≤ it); otherwise refused.  `?` and `:` at the column open new
  entries and stay legal (§6), and `- a⏎? k⏎: v` is pipeline-ACCEPTED
  through the parser's artifact-token leniency, which is what keeps the
  mechanism scoped to `-` alone.

All three reuse `.invalidBareDocument`; on every probed input the
parser's message AND position are what the scanner check would produce,
so the migration is byte-invisible to the matrix and eventscore.

**The price, measured (and why this landed as a map, not a build).**
The emitter-scannability trees re-verify the scanning of emitted output
through `scanNextToken`'s decomposition: the `scanNextToken_via_*`
composition lemmas have ~105 call sites across ~20 files in the two
trees, the `dispatchStructural`-shape facts ~145 references, and
`scanBlockEntry` 276 references.  Every placement of a new refusal —
a new bind in `scanNextToken`'s chain, a throw inside
`dispatchStructural`, or one inside `scanBlockEntry` — lands its
discharge burden on one of those ladders, a 100+-site absorption PER
MECHANISM.  So the refusal half is at least three items (one mechanism
plus its absorption each), not one, and this guard pins today's
verdicts so each landing flips its section loudly and intentionally.

§2–§4 pin the gap (`parserGap`: both scanners accept, both pipelines
refuse); §5 the neighbors the scanner already refuses; §6 the valid
boundary each mechanism must not cross. -/

namespace L4YAML.Tests.Guards.ScannerRaisedFlagRefusalMap

open L4YAML L4YAML.Scanner

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

/-- Both pipelines refuse. -/
private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-- Both pipelines accept (event shape not pinned). -/
private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

/-- Both SCANNERS accept the input outright. -/
private def scansClean (input : String) : Bool :=
  match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
  | .ok _, .ok _ => true
  | _, _ => false

/-- THE GAP: the scanner accepts what the parser refuses (§9.2).  Every
    pin below is an input the tightening needs the SCANNER to refuse. -/
private def parserGap (input : String) : Bool :=
  scansClean input && refuses input

/-- The neighbors already refused at the scanner itself. -/
private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) && refuses input

-- §2 M1 — the completed root document, then content on a later line.
-- Flow close at the root:
#guard parserGap "[1, 2]\na\n"
#guard parserGap "[1, 2]\n[3]\n"
#guard parserGap "[1, 2]\na: 1\n"
#guard parserGap "[1, 2]\n- y\n"
#guard parserGap "[1, 2]\n? k\n"
#guard parserGap "[1, 2]\n: v\n"
#guard parserGap "[1, 2]\n|\n  x\n"
#guard parserGap "[1, 2]\n\"q\"\n"
#guard parserGap "[1, 2]\n&p a\n"
#guard parserGap "[1, 2]\n!t x\n"
#guard parserGap "{a: b}\nx\n"
#guard parserGap "[1, 2] # c\na\n"
#guard parserGap "[1, 2]\n  a\n"
#guard parserGap "[1,\n 2]\na\n"
-- Quoted scalar at the root:
#guard parserGap "\"x\"\na\n"
#guard parserGap "\"x\"\na: 1\n"
#guard parserGap "\"x\"\n: v\n"
#guard parserGap "\"x\"\n[1]\n"
#guard parserGap "\"x\"\n\"y\"\n"
#guard parserGap "\"x\"\n  a\n"
#guard parserGap "\"x\"\n? k\n: v\n"
-- Block scalar at the root (the landing IS the later line):
#guard parserGap "|\n  x\na\n"
#guard parserGap "|\n  x\nb: 2\n"
#guard parserGap "|\n  x\n- y\n"
#guard parserGap "|\n  x\n[1]\n"
#guard parserGap "|\n  x\n: v\n"
#guard parserGap "|2\n  x\na\n"
-- Plain scalar at the root: the walk absorbs continuation lines, so the
-- completed-scalar state is reachable only where the walk stops — a
-- comment line.  (`hello⏎world` is ONE scalar; §6.)
#guard parserGap "hello\n# c\nworld\n"
#guard parserGap "hello\n# c\nw: 1\n"
#guard parserGap "hello\n# c\n: v\n"
-- The explicit-document twins (`---` pushes no indent level):
#guard parserGap "---\na: 1\nb\n"
#guard parserGap "--- [1]\nx\n"
#guard parserGap "--- |\n  q\nx\n"
#guard parserGap "--- \"x\"\na\n"

-- §3 M2 — the dangling node run at an open level's column.
-- Plain danglers at a mapping's column (mid-stream and EOF deaths):
#guard parserGap "a: 1\nb\n"
#guard parserGap "a: 1\nb\nc: 2\n"
#guard parserGap "a: 1\n\"q\"\n"
#guard parserGap "a:\n  b: c\nd\n"
#guard parserGap "a:\nb\nc\n"
-- ...at a sequence's column:
#guard parserGap "- a\nb\n"
#guard parserGap "- a\nb\n- c\n"
#guard parserGap "- a\n\"q\"\n"
-- ...after a completed flow value (the level survives the close):
#guard parserGap "k: [1, 2]\nb\n"
#guard parserGap "- [1, 2]\nb\n"
-- Property-run and alias danglers (the run's START carries the column):
#guard parserGap "x: &q 1\n*q\n"
#guard parserGap "x: &q 1\n*q\ny: 2\n"
#guard parserGap "a: 1\n&p b\n"
#guard parserGap "a: 1\n&p b\nc: 2\n"
#guard parserGap "a: 1\n&p\n"
#guard parserGap "a: 1\n&p\nc: 2\n"
-- Block-scalar danglers at a level's column:
#guard parserGap "k: 1\n|\n  x\n"
#guard parserGap "k: 1\n|\n  x\nm: 2\n"
#guard parserGap "k:\n  a: 1\n|\n  x\n"
-- The dangler dies at a MARKER dispatch too, so the check precedes the
-- structural dispatch:
#guard parserGap "a: 1\nb\n...\n"
#guard parserGap "a: 1\nb\n--- c\n"

-- §4 M3 — the `-` at a mapping top's own column, entry complete.
#guard parserGap "a: 1\n- y\n"
#guard parserGap "a: 1\n- y\nb: 2\n"
#guard parserGap "? k\n- y\n"
#guard parserGap "? k\n- y\n: v\n"
#guard parserGap ": v\n- y\n"
#guard parserGap "a:\n  b:\n  - x\n- y\n"
#guard parserGap "a:\n- x\nb: 1\n- y\n"

-- §5 The neighbors the scanner ALREADY refuses — the map's boundary with
-- the existing checks (§8.1 under-indent, §8.2.1 trailing content, §7.4
-- implicit-key line, §7.3.2/§7.4 same-line junk, §9.1.5 directives):
#guard scannerRefuses "a: 1\n[1]\n"
#guard scannerRefuses "- a\n[1]\n"
#guard scannerRefuses "- a\nb: 2\n"
#guard scannerRefuses "hello\nb: 2\n"
#guard scannerRefuses "[1, 2], x\n"
#guard scannerRefuses "a: 1\n%YAML 1.2\n--- b\n"

-- §6 The valid boundary each mechanism must not cross.
-- M2's three exempt structural predecessors — the equal-column VALUE
-- readings (`.value`, `.key`, `.blockEntry`):
#guard emits "a:\nb\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "?\nb\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :b", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "-\nb\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard accepts "a:\nb\nc: 2\n"
-- M3's two legal readings — the awaited value (with and without a
-- property run) and the continuing same-indent sequence (including the
-- level pops the back-scan must survive):
#guard emits "a:\n- y\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :y", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard accepts "a:\n- y\n"
#guard accepts "a: &x\n- y\n"
#guard accepts "a: !!seq\n- y\n"
#guard emits "a:\n- m:\n    - x\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "+MAP", "=VAL :m",
   "+SEQ", "=VAL :x", "-SEQ", "-MAP", "=VAL :y", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "? k\n:\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :y", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- `?` and `:` at the mapping's column open new ENTRIES — M3 is `-` only:
#guard emits "a: 1\n? k\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :k", "=VAL :v",
   "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :", "=VAL :v",
   "-MAP", "-DOC", "-STR"]
-- ...and the parser's artifact-token leniency ACCEPTS this one, which is
-- what keeps M3 away from `?` at a sequence's column:
#guard accepts "- a\n? k\n: v\n"
-- M1's same-line boundary — the `:` that resolves the completed node as
-- an implicit key never crosses a line:
#guard emits "[1, 2]: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard accepts "\"x\": 1\nb: 2\n"
#guard emits "? \"x\"\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"x", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- M1's completing set excludes plain continuations, properties, markers:
#guard emits "hello\n[1]\n"
  ["+STR", "+DOC", "=VAL :hello [1]", "-DOC", "-STR"]
#guard accepts "hello\nworld\n"
#guard accepts "--- a\nb\n"
#guard emits "&p 1\nx\n"
  ["+STR", "+DOC", "=VAL &p :1 x", "-DOC", "-STR"]
#guard emits "&p\nc: 2\n"
  ["+STR", "+DOC", "+MAP &p", "=VAL :c", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard accepts "[1, 2]\n# c\n"
#guard accepts "\"x\"\n\n"
-- The suffix and explicit-document escapes stay open (items 116–118):
#guard accepts "[1, 2]\n...\na\n"
#guard accepts "a: 1\n...\n[1]\n"
#guard accepts "|\n  x\n...\n- y\n"
#guard accepts "\"x\"\n...\na\n"
#guard accepts "[1, 2]\n--- a\n"
#guard accepts "a: 1\n...\n%YAML 1.2\n--- b\n"
-- Entry continuations at the level's column resolve and never dangle:
#guard accepts "a: 1\nb: 2\n"
#guard accepts "a: 1\n\"q\": 2\nb: 3\n"
#guard accepts "- a\n- b\n"

/-! §7 One pipeline-refused shape rides OUTSIDE the §9.2 family: the
props-only run whose structural predecessor is `.value`
(`a:⏎&p⏎- y`) is refused downstream as `trailing content`, not as
`invalidBareDocument`, while `&p⏎c: 2` (the root twin) is a legal
anchored mapping.  M2's `.value` exemption therefore leaves it to the
parser, and whichever item lands M2 inherits it as a named residue. -/
#guard scansClean "a:\n&p\n- y\n"
#guard refuses "a:\n&p\n- y\n"
#guard accepts "&p\nc: 2\n"

/-! §8 A measured SCANNER asymmetry, found by these pins: same-line junk
after a completed root flow close or quoted scalar is refused by the
LEGACY scanner (`validateFlowClose` / `validateTrailingContent`) but
accepted by the INDEXED one, which leaves it to the parser (verdict
parity holds; the LAYER differs).  The comma twin is symmetric.  M1's
landing inherits the indexed same-line boundary as its own obligation. -/
private def legacyOnlyScanRefusal (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .ok _ => true
   | _, _ => false) && refuses input

#guard legacyOnlyScanRefusal "[1, 2] x\n"
#guard legacyOnlyScanRefusal "\"x\" y\n"

end L4YAML.Tests.Guards.ScannerRaisedFlagRefusalMap
