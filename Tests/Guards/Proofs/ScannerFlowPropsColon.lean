import L4YAML.Output.Events
import L4YAML.Output.EventsIx
import L4YAML.Scanner.Scanner
import L4YAML.Scanner.IndexedDispatch

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A `:` with a `[96] c-ns-properties` run held before it (DOCS item 9o)

Item 9n split the `:` step by the frame TAIL.  This file is about the SECOND
index on the same step — the interior gap, which is either empty or holds a
scanned-but-unattached property run — and about what crossing the two indices
does to the pricing (Reflection 629).

The property run turns out to decorate the entry's KEY, whose content is empty:

    [161] ns-flow-node(n,c) ::= c-ns-alias-node
                              | ns-flow-content(n,c)
                              | ( c-ns-properties(n,c)
                                  ( ( s-separate(n,c) ns-flow-content(n,c) )
                                  | e-scalar ) )

so `[&a : b]` is `SFlowSeqEntry.pairValue` with `SFlowNode.propsEmpty` as its
key — the same node `receivePropsEmpty` builds when a `,` or a close decides the
run, one dispatch later.  §1 and §2 pin those shapes on the two tail classes that
are TOTAL there (`.sep` and `.question`), which is what
`FlowOpenStack.receiveColonPropsSep` / `.receiveColonPropsQuestion` construct.

§3 is the crossing's payoff.  `InteriorGap.props` carries `tl ≠ .value` as a
*field*, so the props × `.value` cell is not a case anybody has to write — it is
not a state.  The shapes that would reach it are rejected by item 9b's
`scanNextToken_checkFlowAdjacency`, which shipped nine items earlier: a property
may not stand directly after a completed flow value.  On the white row the same
tail is the MIXED class, the one cell nothing closes for free.

§4 pins the props × `.colon` cell as still open, alongside the white row's two:
those three shapes are rejected today only by the PARSER, and one strictening of
`scanValueValidate` (DOCS item 9n / Reflection 617) moves all of them to the
scanner at once.  They are listed here so the eventual strictening lands against
recorded behaviour rather than against a diff.
-/

namespace Tests.Guards.ScannerFlowPropsColon

open L4YAML
open L4YAML.Events
open L4YAML.Scanner

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection.
    Equal pairs mean the two pipelines agree. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match streamToEvents input with | .ok s => some s | .error _ => none)
  , (match streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Legacy and indexed SCANNER verdicts as a comparable pair. -/
private def scanVerdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` in the SCANNER, with the same error. -/
private def rejectsInScanner (input : String) (e : ScanError) : Bool :=
  scanVerdicts input == (some e, some e)

/-- Both pipelines SCAN `input` clean but reject it downstream (no events).
    The shape of a gap that only the parser closes. -/
private def scansCleanButRejected (input : String) : Bool :=
  scanVerdicts input == (none, none) && bothEvents input == (none, none)

/-! ## §1  The `.sep` tail with a run held — `receiveColonPropsSep`

`betweenEmpty` (right after the bracket) and `betweenHeld` (right after a `,`)
are the only two frames that index admits, and a properties-only key is an
`ns-flow-node` after both. -/

-- `[&a : b]` — the anchor is on the entry's KEY, not on the entry.
#guard emits "[&a : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- …with an empty value too (`[148]`'s `e-node` branch).
#guard emits "[&a :]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- The tag half of `[96]` alone.
#guard emits "[!t : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- Both halves, in either order — `PropsRun`'s `anchorThenTag` / `tagThenAnchor`.
#guard emits "[&a !t : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[!t &a : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

-- The `betweenHeld` frame: the run opens the entry AFTER a `,`.
#guard emits "[a, &x : b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a", "+MAP {}", "=VAL &x :", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]

#guard emits "[&a : b, &c : d]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP",
   "+MAP {}", "=VAL &c :", "=VAL :d", "-MAP", "-SEQ", "-DOC", "-STR"]

-- The mapping twin of both frames.
#guard emits "{&a : b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP", "-DOC", "-STR"]

#guard emits "{!t : b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL <!t> :", "=VAL :b", "-MAP", "-DOC", "-STR"]

#guard emits "{a: b, &c : d}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "=VAL &c :", "=VAL :d",
   "-MAP", "-DOC", "-STR"]

/-! ## §2  The `.question` tail with a run held — `receiveColonPropsQuestion`

Here the run decorates the EXPLICIT key, so the frame lands in
`midExplicitColon` rather than `midQuestionEmptyColon`: `? &a :` is the `? `
shape whose key is a real `ns-flow-node` after all, just an empty one. -/

#guard emits "[? &a : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[? !t : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL <!t> :", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[? &a :]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL &a :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "{? &a : b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL &a :", "=VAL :b", "-MAP", "-DOC", "-STR"]

/-! ## §3  The props × `.value` cell is NOT A STATE (item 9b, item 9o)

A property run may not stand directly after a completed flow value, so the cell
that is MIXED on the white row is empty on this one.  `InteriorGap.props` records
that as its `tl ≠ .value` field; the scanner records it as `invalidFlowEntry`,
one dispatcher before block-indicator dispatch is even reached. -/

#guard rejectsInScanner "[\"a\" &x : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[\"a\" !t : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[[a] &x : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[[a] !t : b]\n" (.invalidFlowEntry 0 5)
#guard rejectsInScanner "[{a: b} &x : c]\n" (.invalidFlowEntry 0 8)

/-! ## §4  A SECOND `:` in one entry — rejected at the LEGACY scanner (item 9r)

Three cells, one obligation, now discharged on the legacy side: the
`scanValueValidate` strictening rejects all seven shapes at the SCANNER, because
the pending simple key it reads was reserved at the `:` itself when the gap is
empty and BEFORE the run when it is not, and the slot below that reservation is
a `.value` exactly in the illegal shapes.

The INDEXED scanner still scans them clean — its strictening is blocked on an
Ix saved-key substrate (no layout exposure exists on that side yet; see the
item 9r section of `DOCS.md` for the measured budget), so on that pipeline the
parser is still the refusing stage.  This DELIBERATE, DOCUMENTED divergence is
pinned here exactly so the Ix landing is measured against a record, the same
way this section once pinned the pre-strictening state for the legacy landing. -/

/-- Item 9r's intermediate state: the LEGACY scanner rejects `input`, the
    INDEXED scanner scans it clean, and neither pipeline emits events. -/
private def rejectedByLegacyScannerOnly (input : String) : Bool :=
  (match scanVerdicts input with
   | (some _, none) => true
   | _ => false) && bothEvents input == (none, none)

-- White row, `.colon` cell.
#guard rejectedByLegacyScannerOnly "[a: : b]\n"
#guard rejectedByLegacyScannerOnly "[: :]\n"
#guard rejectedByLegacyScannerOnly "{a: : b}\n"
#guard rejectedByLegacyScannerOnly "[? : : a]\n"

-- White row, `.value` cell (the mixed one): the entry is already complete.
#guard rejectedByLegacyScannerOnly "[a: b: c]\n"

-- Props row, `.colon` cell: the run sits between the two `:`s and changes
-- nothing, because the reservation slot is older than the run.
#guard rejectedByLegacyScannerOnly "[a: &x : b]\n"
#guard rejectedByLegacyScannerOnly "[a: !t : b]\n"

/-! ## §5  The run's other decisions, unchanged

`receivePropsEmpty`'s own shapes, re-pinned so that adding a `:` exit from a
held run is visible as additive. -/

#guard emits "[&a]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL &a :", "-SEQ", "-DOC", "-STR"]

#guard emits "[&a, b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL &a :", "=VAL :b", "-SEQ", "-DOC", "-STR"]

-- …and `receivePropsContent`'s: the run decorates the node that follows.
#guard emits "[&a b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL &a :b", "-SEQ", "-DOC", "-STR"]

end Tests.Guards.ScannerFlowPropsColon
