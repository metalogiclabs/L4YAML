import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The park face, and `KeyPackPunt.noFrame`'s deletion (DOCS item 125)

U2 of the under-indent map (`UnderIndentInvariantMap`) asked for the park's
`?`-frame face as a mandatory conditional field on `explicitKeyLine`.  What
the item MEASURED is one construct over, and cheaper: the coupling is not a
park field at all.

* `pendingMapValue.h_ivl` is stamp-or-FACE — the right disjunct is the same
  `[185] s-l+block-indented` slot `h_vslot` already carries.  Every producer
  pays one side outright: the `?` openers (landed and compact) and the
  explicit `:` hand the face they hand `h_vslot`; the four implicit `:`
  producers hand a REAL stamp.
* The stamp is real because the landed-`:` CONSUMERS decide it: a `:` whose
  dispatch state has no live `explicitKeyLine`, or stands off `explicitKeyCol`,
  computed `explicitValue = false` and stamped (item 124's two line-free
  discriminators, joined as `scanValue_stamp_of_src`); a `:` that RESOLVES a
  key stamps whatever the register holds (`scanValue_stamp_of_key`).
* So the pack lemmas' same-line branch is total: frame from `h_compact`, or
  face from the field, or stamp.  `KeyPackPunt.noFrame` — the reason with no
  named input since item 105 — is GONE, and with it the third of the five
  arms every punt consumer had to carry.

What is NOT closed, and is stated here so the next reader does not re-derive
it: the COLLAPSE lane.  A flow collection that renounced its grammar reading
(`FlowStackB.shape`) restores the scanner's register pair at its close while
the surface side keeps no face, so `? [a]⏎: b: c` reaches the landed `:` with
a live register at the `:`'s own column and nothing to pay the explicit route
with.  That input is ACCEPTED by the scanner and DEFERS on the proof side —
the same escape it took before this item, now reached by an undecided source
rather than by a punt.  §3 pins that boundary.

§1 pins the field's two shapes and the deletion; §2 the consumer's own
discriminator; §3 the accepted/refused families on both pipelines. -/

namespace L4YAML.Tests.Guards.ParkFaceCoupling

open L4YAML L4YAML.Scanner L4YAML.Surface

/-! ## §1  The field, and what the constructor no longer has

`KeyPackPunt` has FOUR reasons.  A `match` that covers them is total, which
is what pins the deletion: were `noFrame` still there, this would not
elaborate. -/

example {sc : ScannerState} (h : L4YAML.Proofs.StreamAccum.KeyPackPunt sc) : True :=
  match h with
  | .tab _ _ => trivial
  | .dedent => trivial
  | .implicitValue _ _ _ => trivial
  | .noKeyContext => trivial

-- The field's landed type, read off the constructor itself: a `pendingMapValue`
-- hands stamp-or-FACE, and the face is the park's own `[185]` value slot.  The
-- `have`'s explicit type is the pin — either disjunct changing breaks it.
example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}
    (h : L4YAML.Proofs.StreamAccum.PendingNode sc false sp_start sp_block sp_scan) :
    True := by
  cases h with
  | pendingMapValue _ _ _ n _ _ _ _ h_ivl =>
    have : sc.implicitValueLine = some sc.line ∨
        (sp_scan.col = n + 1 ∧ ∀ sp_v : SurfPos,
          SBlockIndented n .blockOut sp_scan sp_v → SLYamlStream sp_start sp_v) := h_ivl
    trivial
  | _ => trivial

/-! ## §2  The consumer's own discriminator

The landed `:` reads its dispatch state, not the park: no live register, or a
column that differs, means the epilogue stamped. -/

example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' → s.inFlow = false → s.peek? = some ':' →
    (s.explicitKeyLine = none ∨ (s.col : Int) ≠ s.explicitKeyCol) →
    s'.implicitValueLine = some s'.line :=
  fun h1 h2 h3 h4 => L4YAML.Proofs.StreamAccum.scanValue_stamp_of_src h1 h2 h3 h4

/-! ## §3  The families, on both pipelines -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- The face payers: a `?` frame's key slot and an explicit `:`'s value slot,
-- both same-line and across a break.  These are what the field's right
-- disjunct carries, and what the pack lemmas' same-line branch composes
-- through instead of punting.
#guard accepts "? a: b\n"
#guard accepts "?\n: b: c\n"
#guard accepts "? a\n: b: c\n"
#guard accepts "- ? a: b\n"
#guard accepts "? &p a: 1\n"
#guard accepts "?\n: &p a: 1\n"

-- The stamp payers: a `[189]` implicit value whose slot has no compact
-- alternative — the second value indicator on a stamped line is REFUSED, and
-- that refusal is what the field's left disjunct records.
#guard refuses "k: a: 1\n"
#guard refuses "k: &p a: 1\n"

-- The keyed `:` under a live `?` register stamps for the OTHER reason (the
-- resolved key), which is what `colon_open_map_implicit`/`_props` pay with.
#guard emits "? earth: blue\n: moon: white\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :earth", "=VAL :blue", "-MAP",
   "+MAP", "=VAL :moon", "=VAL :white", "-MAP", "-MAP", "-DOC", "-STR"]

-- The COLLAPSE lane's residue, pinned as a BOUNDARY rather than a claim:
-- the scanner accepts these (the restored register pair off a renounced flow
-- collection), and the proof side reaches them with an undecided stamp
-- source and defers.  A later item that gives `FlowStackB.shape` a face slot
-- is what turns these into compositions.
#guard accepts "? [a]\n: b: c\n"
#guard accepts "? {x: y}\n: b: c\n"

-- …and the same shapes WITHOUT the collapse, which compose today.
#guard accepts "? [a]\n: v\n"
#guard accepts "? a\n: v\n"

end L4YAML.Tests.Guards.ParkFaceCoupling
