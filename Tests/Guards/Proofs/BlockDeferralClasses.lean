import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The block-indicator escape, by CLASS and by ROUTE (DOCS items 184–185)

`block_dispatch_deferred` is `PendingNode.pendingFlow`'s only producer, so
R3 — row 12's β.5 deletion — is the emptying of this escape.  Its applications
have been counted since item 183 (`FlipConsumerSurface`, FIVE definitions and
TWELVE applications), and the count is not the price: an escape's price is its
DOMAIN, and the two are independent in both directions (Reflection 645).

Item 184 partitioned the twelve by the branch that reaches them, in the CODE
rather than in prose, and read 9 stamp / 2 inline / 1 bare.  Item 185 measured
the NINE and found them three questions with three different prices — the
consumer splits again on the park's value pack, and the two compact sites take
a different route entirely.  Each wrapper carries its branch's own hypothesis,
so the assignment is checked by the elaborator and a class emptying is a
wrapper's deletion rather than a total drifting:

| wrapper | applications | what reaches it | what empties it |
|---|---|---|---|
| `_stamp_offcol` | **3** in 3 definitions | the park HAS a value pack, at `nv`, and the landing is at `k ≠ nv` | a reason the two indices agree — `[187]`'s `s-indent(n)` is exact |
| `_stamp_nopack` | **4** in 4 definitions | the park carries no value pack at all | a CARRIER: the `?` frame's value slot at the landing's column, U2's residue proper |
| `_stamp_compact` | **2** in 2 definitions | the fill is COMPACT, and `[189]`'s value is `s-l+block-node`, so the face cannot stand in for the stamp | the stamp, or a refutation |
| `_inline` | **2** in 2 definitions | the mid-line indicator (`inline_residue_of_landing`) | `KeyPackPunt`'s two surviving reasons (item 102) |
| bare | **1** | `pendingFlow`'s own arm, which this escape PRODUCES | the constructor (item 35's structural note) |

**The classes OVERLAP; only the sites are partitioned.**  `_stamp_compact`'s
two sites hold the inline residue's discriminator as well, and their premise
records both — so item 184's three "classes" are three branches of the proof,
not three disjoint sets of inputs, and a wrapper's count is a count of SITES.

**What the three stamp wrappers now share** (item 185).  `scanValue`'s
`explicitValue` is a conjunction of three tests and item 125's split read two
of them, so the escape's branch was the negation of a disjunction WEAKER than
`explicitValue = true` and had nothing to spend.  With
`scanValue_stamp_of_cleared_key` supplying the third alternative the split is
total: the branch's premise IS `explicitValue = true`, the `:` is `[197]
l-block-map-explicit-value`'s own, and — since the scanner ADMITTED it —
`explicit_at_indent_of_dispatch` reads `s-indent(n)` off the same state.  Every
one of the nine sites produces that equation, so the datum a route into the `?`
frame's value slot has to land on is known present at ALL of them rather than
at the ones a reading happened to check.

**None of the live classes is REFUTABLE.**  §2's family is accepted by the
scanner and read identically by PyYAML 6.0.3 at the event level; §3's is the
implicit-key pack's punt, whose own price this file pins beside it.  §4 is the
compact route, whose own family the runtime refuses at every input a sweep of
35 937 three-line programs and all 351 `yaml-test-suite` sources produced — an
emptiness that is measured, not proved, and so a refutation TARGET rather than
a refutation.

**What `_inline` costs, measured two ways that agree.**  The pack's two live
punt reasons are `KeyPackPunt.dedent` (**7** applications in 5 definitions:
both entry-pack producers twice each, and the flow open, the implicit `:` and
the props `:` once each) and `KeyPackPunt.noKeyContext` (**6** in 5: the flow
close's own pack, the routed content dispatch twice, and the same three
consumers once each).  Deleting each constructor and building breaks exactly
those applications, and `FlipConsumerSurface`'s PACK PUNT lane counts the same
rows from the elaborated environment — a narrowing patch and an environment
census, agreeing row for row.

`noKeyContext` has no NAMED input (item 102 left it "a frame class rather than
a construct"), which by Reflection 646 is the signature of a branch that may be
a phantom; `dedent`'s is `k:⏎  :⏎b: 2`, §3's first row.  Both are pinned below
as the boundary, not as a claim about which of the two the escape needs. -/

namespace L4YAML.Tests.Guards.BlockDeferralClasses

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.CouplingBridge

/-! ## §1  The wrappers, pinned by APPLICATION

Each `example` applies its wrapper at the exact hypotheses the branch holds.
A wrapper that loses a premise — or gains one — fails to elaborate here, so the
class's definition cannot drift away from what the DOCS record says it is. -/

/-- The three stamp wrappers' SHARED premise, named once: item 125's split
    taken negatively, with item 185's third alternative in it, beside the
    `s-indent(n)` equation the same state then yields. -/
private def StampBranch (s_dis : ScannerState) : Prop :=
  ¬(s_dis.explicitKeyLine = none ∨
    (scanValueClearKey s_dis).simpleKey.possible = true ∨
    (s_dis.col : Int) ≠ s_dis.explicitKeyCol)

/-- …and that it is exactly what the dispatch's own admission reads
    `s-indent(n)` off.  This is the branch's residue as DATA. -/
example {s_dis s' : ScannerState}
    (h_dispatch : scanNextToken_dispatchBlockIndicators s_dis ':' = .ok (some s'))
    (h_noflow : s_dis.inFlow = false) (h : StampBranch s_dis) :
    (s_dis.col : Int) = s_dis.currentIndent :=
  explicit_at_indent_of_dispatch h_dispatch h_noflow h

/-- The split is TOTAL: all three alternatives stamp, so the branch above is
    the complement of the stamp rather than a part of it. -/
example {s s' : ScannerState}
    (h : scanValue s = .ok s') (h_noflow : s.inFlow = false)
    (h_peek : s.peek? = some ':')
    (h_src : s.explicitKeyLine = none ∨
      (scanValueClearKey s).simpleKey.possible = true ∨
      (s.col : Int) ≠ s.explicitKeyCol) :
    s'.implicitValueLine = some s'.line :=
  scanValue_stamp_of_src h h_noflow h_peek h_src

/-- `offcol`: the pack's index and the landing's, and the disequality between
    them — `colon_open_map_explicit` fires only when they agree. -/
example (sp_start sp_X sp_scan' : SurfPos) (s' s_dis : ScannerState) (nv k : Nat)
    (h_stream : SLYamlStream sp_start sp_X)
    (h_arm : s'.simpleKeyAllowed = true ∨ 0 < sp_scan'.col)
    (hcorr : ScannerSurfCorr s' sp_scan')
    (h_nodir : s'.allowDirectives = false)
    (h_src : StampBranch s_dis)
    (h_indent : (s_dis.col : Int) = s_dis.currentIndent)
    (h_ne : nv ≠ k) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan'',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none 0 #[] #[] .sep sp_block' sp_flow' ∧
      PendingNode s' false sp_start sp_flow' sp_scan'' ∧
      ScannerSurfCorr s' sp_scan'' :=
  block_dispatch_deferred_stamp_offcol sp_start sp_X sp_scan' s' h_stream h_arm
    hcorr h_nodir h_src h_indent h_ne

/-- `nopack`: the same, with NOTHING about the pack.  The field's other
    alternative is `True`, so there is no proposition to carry and the census
    row is this class's only instrument. -/
example (sp_start sp_X sp_scan' : SurfPos) (s' s_dis : ScannerState)
    (h_stream : SLYamlStream sp_start sp_X)
    (h_arm : s'.simpleKeyAllowed = true ∨ 0 < sp_scan'.col)
    (hcorr : ScannerSurfCorr s' sp_scan')
    (h_nodir : s'.allowDirectives = false)
    (h_src : StampBranch s_dis)
    (h_indent : (s_dis.col : Int) = s_dis.currentIndent) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan'',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none 0 #[] #[] .sep sp_block' sp_flow' ∧
      PendingNode s' false sp_start sp_flow' sp_scan'' ∧
      ScannerSurfCorr s' sp_scan'' :=
  block_dispatch_deferred_stamp_nopack sp_start sp_X sp_scan' s' h_stream h_arm
    hcorr h_nodir h_src h_indent

/-- `compact`: the stamp branch AND the inline residue, which is what says the
    two classes overlap at these two sites. -/
example (sp_start sp_X sp_scan' sp_park : SurfPos) (s' s_dis : ScannerState)
    (c : Char)
    (h_stream : SLYamlStream sp_start sp_X)
    (h_arm : s'.simpleKeyAllowed = true ∨ 0 < sp_scan'.col)
    (hcorr : ScannerSurfCorr s' sp_scan')
    (h_nodir : s'.allowDirectives = false)
    (h_src : StampBranch s_dis)
    (h_indent : (s_dis.col : Int) = s_dis.currentIndent)
    (h_res : InlineResidue sp_park c) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan'',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none 0 #[] #[] .sep sp_block' sp_flow' ∧
      PendingNode s' false sp_start sp_flow' sp_scan'' ∧
      ScannerSurfCorr s' sp_scan'' :=
  block_dispatch_deferred_stamp_compact sp_start sp_X sp_scan' s' h_stream h_arm
    hcorr h_nodir h_src h_indent h_res

/-- The inline class's premise is `inline_residue_of_landing`'s conclusion: the
    park is off column 0 and only `s-white` stands between it and the
    indicator. -/
example (sp_start sp_X sp_scan' sp_park : SurfPos) (s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_X)
    (h_arm : s'.simpleKeyAllowed = true ∨ 0 < sp_scan'.col)
    (hcorr : ScannerSurfCorr s' sp_scan')
    (h_nodir : s'.allowDirectives = false)
    (h_res : InlineResidue sp_park c) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan'',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none 0 #[] #[] .sep sp_block' sp_flow' ∧
      PendingNode s' false sp_start sp_flow' sp_scan'' ∧
      ScannerSurfCorr s' sp_scan'' :=
  block_dispatch_deferred_inline sp_start sp_X sp_scan' s' h_stream h_arm hcorr
    h_nodir h_res

/-- `InlineResidue`'s own shape, pinned: the class is about a park OFF a line
    start, which is what makes it the mid-line `:` rather than a landing. -/
example (sp : SurfPos) (c : Char) (h : InlineResidue sp c) : sp.col ≠ 0 := h.1

/-! ## §2  The stamp class's family, at the runtime

`ParkFaceCoupling` §3 pins two inputs as accepted-and-still-deferred; the rows
below say which coordinate of that shape carries the deferral.  The scanner's
verdict and BOTH pipelines' events are pinned, so a runtime move flips this
loudly. -/

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

private def evBoth (input : String) : String :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok a, .ok b => if a == b then flat a else s!"MISMATCH {flat a} ≠ {flat b}"
  | .error a, .error b =>
      if reprStr a == reprStr b then s!"ERR {repr a}" else s!"ERR-MISMATCH {repr a} ≠ {repr b}"
  | .ok a, .error b => s!"SPLIT ok {flat a} / err {repr b}"
  | .error a, .ok b => s!"SPLIT err {repr a} / ok {flat b}"

private def pins (input : String) : String × String := (scanPhase input, evBoth input)

-- The residue itself: a FLOW-collection explicit key whose value is a
-- same-line compact mapping.  PyYAML 6.0.3 (`yaml.parse`) reads both with the
-- same event shape.
#guard pins "? [a]\n: b: c\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :a -SEQ +MAP =VAL :b =VAL :c -MAP -MAP -DOC -STR")
#guard pins "? {x: y}\n: b: c\n" == ("scan-accepted", "+STR +DOC +MAP +MAP {} =VAL :x =VAL :y -MAP +MAP =VAL :b =VAL :c -MAP -MAP -DOC -STR")

-- The same compact value at a PLAIN key, which `ParkFaceCoupling` §3 pins as a
-- face PAYER: so the deferral is not the compact fill by itself.  The props and
-- quoted keys below are measured ACCEPTED here and nothing more — which arm
-- they take is not a runtime question and this file does not claim it.
#guard pins "? a\n: b: c\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a +MAP =VAL :b =VAL :c -MAP -MAP -DOC -STR")
#guard pins "? &p a\n: b: c\n" == ("scan-accepted", "+STR +DOC +MAP =VAL &p :a +MAP =VAL :b =VAL :c -MAP -MAP -DOC -STR")
#guard pins "? \"a\"\n: b: c\n" == ("scan-accepted", "+STR +DOC +MAP =VAL \"a +MAP =VAL :b =VAL :c -MAP -MAP -DOC -STR")

-- …and the same FLOW key with the value shapes `ParkFaceCoupling` §3 pins as
-- composing (`? [a]⏎: v`) or item 96 closed (`? [1]⏎: - w`): so the deferral is
-- not the flow key by itself either.  Both coordinates together carry it.
#guard pins "? [a]\n: v\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :a -SEQ =VAL :v -MAP -DOC -STR")
#guard pins "? [a]\n: - w\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :a -SEQ +SEQ =VAL :w -SEQ -MAP -DOC -STR")
#guard pins "? [a]\n: |\n    x\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :a -SEQ =VAL |x\\n -MAP -DOC -STR")

-- The family's own width: nested and multi-element flow keys, a second entry
-- in the compact value, an indented frame, and an explicit value inside it.
#guard pins "? [a, b]\n: c: d\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :a =VAL :b -SEQ +MAP =VAL :c =VAL :d -MAP -MAP -DOC -STR")
#guard pins "? [[a]]\n: b: c\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] +SEQ [] =VAL :a -SEQ -SEQ +MAP =VAL :b =VAL :c -MAP -MAP -DOC -STR")
#guard pins "? [a]\n: b: c\n  d: e\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :a -SEQ +MAP =VAL :b =VAL :c =VAL :d =VAL :e -MAP -MAP -DOC -STR")
#guard pins "- ? [a]\n  : b: c\n" == ("scan-accepted", "+STR +DOC +SEQ +MAP +SEQ [] =VAL :a -SEQ +MAP =VAL :b =VAL :c -MAP -MAP -SEQ -DOC -STR")
#guard pins "k:\n  ? [a]\n  : b: c\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP +SEQ [] =VAL :a -SEQ +MAP =VAL :b =VAL :c -MAP -MAP -MAP -DOC -STR")
#guard pins "? [a]\n: ? x\n  : y\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :a -SEQ +MAP =VAL :x =VAL :y -MAP -MAP -DOC -STR")

-- The SAME-LINE `:` after a flow key is a different reading and not this
-- class's — the key is implicit there and the `?` entry closes empty.
#guard pins "? [a]: b\n" == ("scan-accepted", "+STR +DOC +MAP +MAP +SEQ [] =VAL :a -SEQ =VAL :b -MAP =VAL : -MAP -DOC -STR")

/-! ## §3  The inline class, and what it is made of

Item 102 measured this class as the implicit-key pack's punt rather than a
shape of its own: the mid-line `:` composes whenever `colon_fires_implicit_key`
gets a pack.  The rows below are the punt's named input, the mid-line `:`
families that DO compose, and the one the runtime refuses outright.

The reference here is the suite, not PyYAML: `k:⏎  :⏎b: 2`'s inner entry has an
empty implicit key, and PyYAML refuses every one of those — its known `[192]`
gap, recorded at item 173, not a datum about this reading. -/

-- `KeyPackPunt.dedent`'s named input (items 39/40/99) and its value twin.
#guard pins "k:\n  :\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL : =VAL : -MAP =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  : v\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL : =VAL :v -MAP =VAL :b =VAL :2 -MAP -DOC -STR")

-- The mid-line `:` that COMPOSES, at each frame the pack serves — the class's
-- lower boundary, and why its runtime shape is an upper bound on it.
#guard pins "a: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC -STR")
#guard pins "k:\n  a: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 -MAP -MAP -DOC -STR")
#guard pins "- a: 1\n" == ("scan-accepted", "+STR +DOC +SEQ +MAP =VAL :a =VAL :1 -MAP -SEQ -DOC -STR")
#guard pins "? a\n: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :b -MAP -DOC -STR")
#guard pins "[1] : b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")

-- …and the mid-line `:` the RUNTIME refuses, so no arm owes it a reading
-- (item 48's `nestedMappingOnLine`).
#guard pins "k: a: 1\n" == ("scan-refused L4YAML.ScanError.nestedMappingOnLine 0 4", "ERR L4YAML.ScanError.nestedMappingOnLine 0 4")

/-! ## §4  The COMPACT route, and why its family is a refutation target

`_stamp_compact`'s two sites are reached only by a `:` — the `?` arm of the
consumers' `hcv.elim` discharges `c = ':'` by `absurd`, and the `-` is handled
before the split — so the shape is a MID-LINE `:` whose dispatch state has a
live `explicitKeyLine` and stands at `explicitKeyCol`.

The register is set by the most recent `?` (or restored by the matching flow
close), so the shape wants a `?` mid-line at column c on one line and a `:`
mid-line at the SAME column on a later one.  Every input of that shape the
measurement found is REFUSED, by §8.2.2 [197]'s own `s-indent(n)` test — the
one `explicit_at_indent_of_dispatch` reads forwards.  Two instruments agree:
a sweep of 35 937 three-line programs over a 33-fragment line alphabet (5 186
accepted, 1 412 of them carrying a landed class-A `:`, **zero** carrying a
compact one) and all 351 `yaml-test-suite` sources (zero of EITHER).

That is an emptiness measured at the runtime, not proved, so this section is a
refutation TARGET.  The rows are the boundary: the `:` shapes the scanner
refuses, and the `?`/`-` neighbours at the same coordinate that it accepts —
which is what says the refusal belongs to the `:`'s own [197] test and not to
the column. -/

-- The compact route's own shape, at three depths: the mid-line `:` standing at
-- a live `explicitKeyCol`.  `currentIndent` is the third number.
#guard pins "- ? a\n- : b\n" == ("scan-refused L4YAML.ScanError.misindentedExplicitValue 1 2 0", "ERR L4YAML.ScanError.misindentedExplicitValue 1 2 0")
#guard pins "- ? [x]\n- : b\n" == ("scan-refused L4YAML.ScanError.misindentedExplicitValue 1 2 0", "ERR L4YAML.ScanError.misindentedExplicitValue 1 2 0")
#guard pins "- - ? a\n- - : b\n" == ("scan-refused L4YAML.ScanError.misindentedExplicitValue 1 4 2", "ERR L4YAML.ScanError.misindentedExplicitValue 1 4 2")

-- The SAME coordinate with a `?` or a `-` instead: accepted, and neither
-- indicator ever reaches the deferral — so the refusal above is the `:`'s.
#guard pins "- ? a\n- ? b\n" == ("scan-accepted", "+STR +DOC +SEQ +MAP =VAL :a =VAL : -MAP +MAP =VAL :b =VAL : -MAP -SEQ -DOC -STR")
#guard pins "- ? a\n- - b\n" == ("scan-accepted", "+STR +DOC +SEQ +MAP =VAL :a =VAL : -MAP +SEQ =VAL :b -SEQ -SEQ -DOC -STR")

-- A mid-line `:` OFF the register's column composes, which is why the class is
-- the coordinate and not the position.
#guard pins "? : a\n: b\n" == ("scan-accepted", "+STR +DOC +MAP +MAP =VAL : =VAL :a -MAP =VAL :b -MAP -DOC -STR")
#guard pins "? ? a\n: b\n" == ("scan-accepted", "+STR +DOC +MAP +MAP =VAL :a =VAL : -MAP =VAL :b -MAP -DOC -STR")
#guard pins "? - a\n: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ =VAL :a -SEQ =VAL :b -MAP -DOC -STR")

end L4YAML.Tests.Guards.BlockDeferralClasses
