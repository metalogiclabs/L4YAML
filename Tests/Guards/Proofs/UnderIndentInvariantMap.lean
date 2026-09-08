import L4YAML.Scanner.Scanner
import L4YAML.Scanner.IndexedDispatch
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The under-indent invariant, measured (DOCS item 121)

Items 101/104/105/107 each deferred a residue to "the under-indent
invariant", and item 118's ledger carried it as ONE multi-session item.
This item measured what the name actually covers, and — like item 119's
finding one item over — it is THREE couplings, not one, each with its own
carrier, consumer, and price:

* **U1 — the `?`-line column bound (scanner-internal, KeysBehindCursor-
  shaped)**: at a boundary whose live candidate is saved on an EARLIER
  line, the CURSOR sits strictly past `currentIndent`.  [Item 122
  CORRECTED this bullet: it originally bounded the KEY's column against
  `explicitKeyCol` — a true fact that cannot refute the pair, whose
  decidable half is about the cursor; `ScalarWalkCrossLineFloor` §1 is
  the machine-checked witness.]  Serves item 104's stale-key PAIR (the
  `?`-line arm of `scanValueClearKey`), replacing the disjunction's
  deferred arm with a refutation.  Repriced by item 122 (the walks' own
  floors landed first, `ScalarWalkColFloor`) and CLOSED by item 123:
  `StaleCursorFloor.StaleKeyCursorFloor` is the invariant,
  `scanNextToken_preserves_StaleKeyCursorFloor` its clone of item 81's
  skeleton, and `colon_fires_implicit_key`'s pair punt is spent
  (`StaleCursorFloorInvariant` is the guard).
* **U2 — the park-face coupling (scanner ↔ SURFACE)**: `sc.explicitKeyLine
  = some l` at a park implies the park's `?`-frame face (`h_expl` /
  `h_vslot`) is REAL — stated as a mandatory conditional field in the
  named-family style.  This is the one item 105 measured as REQUIRED for
  `KeyPackPunt.noFrame`'s deletion: `scanValue` stamps only when
  `explicitValue` is false, `explicitValue` reads `explicitKeyLine`, and
  the two keyless `:` branches produce IDENTICAL scanner states — no
  scanner-internal fact separates them, so the discriminator must be the
  surface face the parks already hold.  The spend deletes `noFrame`
  (`by_cases` on the flag: set → the coupling's real face routes through
  the explicit opener; unset → `explicitValue` is false and the stamp is
  real).  Cost: every producer of the face-carrying parks pays or refutes
  the conditional — the "every pending" threading item 101's §measured
  note priced, a session at least.  [Item 124 landed the SCANNER half:
  `ExplicitKeyCoupling` carries both registers through every scan and
  states the five LINE-FREE `scanValue` discriminators the by_cases
  spends (guard `ExplicitKeyCouplingLadder`); the field redesign, the
  collapse shape's face slot and the deletion are U2b.]
* **U3 — the frames ↔ indent-stack coupling**: the packs' resume-twin
  lists `ks` are SURFACE data; the runtime's misindented-sibling refusal
  reads the SCANNER's indent stack (`scanNextToken_preprocess`'s unwind
  check — §2's pins).  The membership test's deferred case
  (`KeyPackPunt.dedent`'s `w ∉ ks`, items 65/99/109) becomes a refutation
  only when `ks` is coupled to the columns of `sc.indents`' open entries.
  Serves R4's landing pad narrowing; its carrier is an accumulation-
  invariant conjunct, not a park field — the widest of the three.

Order: U1 (self-contained — CLOSED by items 122+123), then U2 (unblocks
`noFrame` → shrinks the `pendingFlow` feed → 67b's deletion with
`noKeyContext`'s twin), then U3 (R4's own).  §1 pins the scanner's `explicitKeyLine` machine on the
runtime; §2 pins U3's refusal family; §3 pins the valid boundary the
couplings must not cross. -/

namespace L4YAML.Tests.Guards.UnderIndentInvariantMap

open L4YAML L4YAML.Scanner

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) && refuses input

-- §1 The `explicitKeyLine` machine at the runtime (U1/U2's substrate).
-- The `?` sets it; the explicit value at the key's column consumes it
-- (`? a⏎: v`); an entry DEEPER than `explicitKeyCol` keeps it live
-- (spec 8.19's compact entries inside the key)…
#guard emits "? a\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "? earth: blue\n: moon: white\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :earth", "=VAL :blue", "-MAP",
   "+MAP", "=VAL :moon", "=VAL :white", "-MAP", "-MAP", "-DOC", "-STR"]
-- …and a keyless `:` SHALLOWER than the `?`'s column ends the entry and
-- opens an empty-key entry at the outer level (item 51's reading):
#guard emits "k:\n  ? a\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :",
   "-MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- U1's family (item 104 §3): an explicit key's continuation lines must
-- clear the `?`, so the stale-candidate PAIR is runtime-refused — the
-- deferred arm U1 will refute has no accepted input behind it.
#guard refuses "? [1,\n 2]: v\n"
#guard refuses "? x\n y: v\n"
#guard refuses "? \"a\n b\": v\n"

-- §2 U3's refusal family: the misindented sibling is the SCANNER's own
-- refusal (the unwind check in `scanNextToken_preprocess` — landing above
-- the new top after a pop), which the surface-side membership punts will
-- read once `ks` is coupled to the indent stack.
#guard scannerRefuses "k:\n    a: 1\n  b: 2\n"
#guard scannerRefuses "k:\n    a: 1\n  b: 2\nc: 3\n"
#guard scannerRefuses "?\n    a: 1\n  b: 2\n: v\n"
#guard scannerRefuses "k:\n  m:\n      x: 1\n    y: 2\n"

-- §3 The valid boundary: siblings AT an open level's own column resume
-- (items 99–118's families — the couplings must not refuse these).
#guard accepts "k:\n    a: 1\n    b: 2\nc: 3\n"
#guard accepts "?\n  a: 1\n  b: 2\n: v\n"
#guard accepts "k:\n  m:\n    x: 1\n  n: 2\n"

end L4YAML.Tests.Guards.UnderIndentInvariantMap
