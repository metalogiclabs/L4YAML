import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # What the entry key pack punts on, and where each one is answered (DOCS item 65)

`entryKeyPack_of_dispatch` used to hand `True` for every shape it could not
read back as `[193]`/`[194]`'s implicit key, so the `:` step that consumes the
pack could not tell one from another and deferred on all of them.  Item 65
replaces that `True` with `KeyPackPunt`'s five named reasons and spends the one
that is the `:`'s own.  Everything below is RUNTIME behavior — none of it
changed at this item; the pins say what the proof's new case split has to be
consistent with.  They pin the SHAPES the reasons name and how the scanner
answers them, not which arm a given input takes: an escape is silent, so no
runtime observation can say that.

* §1 **the tab is the `:`'s to refuse, not preprocessing's.**  A tab in the
  whitespace in front of a KEY sits past `currentIndent`, so §6.1's
  preprocessing gate lets it through and the same run reads fine in front of a
  VALUE.  What refuses `k:⏎␣→a: 1` is `scanValueIndentTabCheck`, one step
  later, walking back from `simpleKey.pos` — which is exactly the reading
  `KeyPackPunt.tab` carries.  The error's own line and column name the KEY, not
  the `:`.
* §2 **and the tab in front of a `:` is legal**, because `[154]`'s trailing
  `s-separate-in-line?` admits `s-white`: only the run in front of the ENTRY is
  `[63] s-indent`.  This is the boundary the refutation must not cross.
* §3 **the key HEAD was never what was missing.**  A block scalar is a node and
  never a key, and the scanner says so by clearing the saved key — the `:` after
  `k: |⏎  x` opens a SECOND entry with an empty key rather than resolving the
  scalar.  An alias IS a key wherever a park offers one.
* §4 **the reasons that remain are claims, not formalities.**  `dedent` and
  `noFrame` each name a shape the scanner ACCEPTS, so the deferral they ride is
  carrying real inputs — row 19's frame stack and item 51's explicit-entry
  threading respectively.  `noKeyContext` is about the CALLER rather than the
  input, and its complement is what is pinnable: where item 56's frame does
  carry a route, the closed flow collection reads as `[194]`'s JSON key. -/

namespace L4YAML.Tests.Guards.ScannerKeyPackPunt

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The same run, twice: a VALUE reads over it and a KEY does not.
#guard emits "k:\n \ta\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  \ta\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
#guard refuses "k:\n \ta: 1\n"
#guard refuses "k:\n  \ta: 1\n"
-- …and the same in a COMPACT entry, where the run is `[185]`'s `s-indent(m)`.
#guard refuses "- \ta: 1\n"
-- The reported position is the KEY's, which is how the check's key branch is
-- told apart from its cursor branch: the `:` sits at column 4 and `a` at
-- column 2, and it is `a`'s that comes back.
private def tabAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.tabInIndentation l c) => some (l, c)
  | _ => none

#guard tabAt "k:\n \ta: 1\n" == some (1, 2)
#guard tabAt "k:\n  \ta: 1\n" == some (1, 3)
#guard tabAt "- \ta: 1\n" == some (0, 3)

-- §2 The boundary the refutation must not cross: `[154]`'s own trailing
-- `s-separate-in-line?` admits a tab, so only the ENTRY's run is `[63]`.
#guard emits "a\t: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]

-- §3 The head is total.  A block scalar never resolves as a key — the `:`
-- below it opens a second entry whose key is `e-node` …
#guard emits "k: |\n  x\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n", "=VAL :", "=VAL :v", "-MAP",
   "-DOC", "-STR"]
-- … and an alias IS one wherever a park offers a frame.
#guard emits "- &x v\n- *x : b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &x :v", "+MAP", "=ALI *x", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]
-- At the document root the same alias key is the SCANNER's refusal, not a
-- missing production.
#guard refuses "&x v\n*x : b\n"

-- §4 The surviving reasons.
-- `dedent` — the landing under-ran the pending's index (item 64's boundary).
#guard emits "k:\n  :\nj: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :j", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- `noFrame` — the key is on the park's own line and the park owns no compact
-- alternative: `[192]`'s explicit entry, whose value is a compact mapping.
#guard emits "? a\n: b: c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :c", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- …and its implicit sibling, which the scanner refuses (§8.2.2 [194]).
#guard refuses "k: a: 1\n"
-- `noKeyContext`'s complement — a closed flow collection as `[194]`'s JSON
-- key, at the two frames item 56 gave routes and at the mapping form.  What
-- the constructor covers is a frame with no route at all, which is a fact
-- about the pending and not about any input.
#guard emits "[1] : b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "- [1] : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "{a: 1} : b\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerKeyPackPunt
