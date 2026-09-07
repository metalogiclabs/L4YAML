import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The auto-detected width has no floor, and the truncation is why (DOCS item 107)

`[183] l+block-sequence(n)` and `[187] l+block-mapping(n)` are
`( s-indent(n+m) … )+` for some auto-detected **`m > 0`**.  `SBlockNode.blockSeq`
and `.blockMap` bind that `m` as a bare `Nat` (item 22 bound it at the right
SCOPE — Reflection 647 — and left its RANGE open), which is row 19's fourth
over-approximation, recorded 2026-08-16 and carried unpriced ever since with the
note "harmless at the root".

This file prices it.  The parameter cannot simply be tightened, because in this
encoding `m = 0` is doing THREE different jobs and only one of them is the
over-approximation:

* the ROOT's own mapping — `a: 1` at column 0 — is `SBlockNode 0`, and its
  entries are at column 0, so the constructor's `n + m` forces `m = 0`.  The
  spec has no such case: the document node is `s-l+block-node(-1, block-in)`,
  so `-1 + 1 = 0` with `m = 1`.
* the SEQ-SPACES key — `?⏎- a`, whose `-` sits at the `?`'s own column — is
  `[201] seq-spaces(n, block-out) = n-1`, which at `n = 0` is the spec's `-1`
  and here is `0 - 1 = 0`.  Truncating subtraction, so again `m = 0`.
* the EQUAL-WIDTH landing — `k:⏎  a: 1⏎  b: 2`'s second key — is the one the
  spec really forbids: a mapping nested inside its enclosing entry at that
  entry's own width, where `parseYaml` reads a SIBLING.

`Nat` cannot tell the first two from the third, and §2 says why in one line:
`seq-spaces` collides at exactly the two indices that matter.  So `0 < m` is not
a one-line tightening of a parameter — it is a re-indexing of `SBlockNode`, and
the plan row that reads "4 construction sites" is pricing the wrong thing.

Everything below is either a RUNTIME pin (no runtime file is touched at this
item) or a TERM whose elaboration is the fact. -/

namespace L4YAML.Tests.Guards.BlockCollectionWidthFloor

open L4YAML L4YAML.Surface L4YAML.Proofs.StreamAccum

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

-- §1 The three families, as the parser reads them.
-- The ROOT mapping: entries at column 0 under the document's own node.
#guard emits "a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- The SEQ-SPACES key: the `-` shares the `?`'s column and is still the key's
-- own sequence, not a sibling of anything.
#guard emits "?\n- a\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL :a", "-SEQ", "+SEQ", "=VAL :w", "-SEQ",
   "-MAP", "-DOC", "-STR"]
#guard emits "?\n- a\n- b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The EQUAL-WIDTH landing: ONE mapping with two entries at width 2 — a
-- sibling, not a nesting.  This is the reading the fourth over-approximation
-- admits a second derivation of.
#guard emits "k:\n  a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b",
   "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
-- …and inside a `?` key, which is where item 106 met it.
#guard emits "?\n  a: b\n  c: d\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]

/-! ## §2 The collision

`[201] seq-spaces(n,c)` is `n-1` in block-out and `n` in block-in, and `n` is a
`Nat` here, so the subtraction truncates.  It truncates at exactly one index —
and that index is the root's. -/

example : seqSpaces 0 .blockOut = 0 := rfl
example : seqSpaces 1 .blockOut = 0 := rfl
/-- The spec's `-1` and the spec's `0` are the same `Nat`. -/
example : seqSpaces 0 .blockOut = seqSpaces 1 .blockOut := rfl
/-- And nowhere else: above the collision the map is injective again. -/
example : seqSpaces 2 .blockOut ≠ seqSpaces 1 .blockOut := by decide
example : seqSpaces 3 .blockOut = 2 := rfl
/-- Block-in never subtracts, so its floor is the honest `n < E`. -/
example (n : Nat) : seqSpaces n .blockIn = n := rfl

/-! ## §3 What each family needs of `m`

The constructor's entries index is `seqSpaces n c + m` (sequence) and `n + m`
(mapping), so each family's own width IS an equation in `m`.  Two of the three
solve to `m = 0`. -/

/-- The ROOT mapping: `n = 0` and entries at column 0. -/
example {s s₂ s' : SurfPos} (h_ssl : SSLComments s s₂)
    (h_entries : SBlockMapEntries 0 s₂ s') : SBlockNode 0 .blockIn s s' :=
  SBlockNode.blockMap 0 .blockIn 0 s s s₂ s' (GOpt.none s) h_ssl h_entries

/-- The SEQ-SPACES key: `n = 0` in block-out and the `-` at column 0. -/
example {s s₂ s' : SurfPos} (h_ssl : SSLComments s s₂)
    (h_entries : SBlockSeqEntries 0 s₂ s') : SBlockNode 0 .blockOut s s' :=
  SBlockNode.blockSeq 0 .blockOut 0 s s s₂ s' (GOpt.none s) h_ssl h_entries

/-- Neither has another solution: the spec's own `m > 0` is unreachable at
    index 0 for as long as the index expression is `n + m` over `Nat`. -/
example : ¬ ∃ m : Nat, 0 < m ∧ 0 + m = 0 := by omega

/-! ## §4 The over-approximation itself

`nestedBlockMap`'s side condition is `n ≤ k` — item 39's, and the whole content
of the landed/dedent split at `entryKeyPack_of_dispatch`.  At `k = n` it is
still satisfied, and what comes out is a mapping nested inside its enclosing
entry at that entry's own width: the derivation the parser's SIBLING reading
has no use for.  This is the term, and it needs nothing but `Nat.le_refl`. -/

example {n : Nat} {s s₂ s' : SurfPos} (h_ssl : SSLComments s s₂)
    (h_entries : SBlockMapEntries n s₂ s') : SBlockNode n .blockIn s s' :=
  nestedBlockMap (Nat.le_refl n) h_ssl h_entries

/-- The honest half of the same split — a STRICTLY deeper landing — is the one
    the spec's `m > 0` would keep, and it is already what every non-degenerate
    caller passes. -/
example {n k : Nat} (hlt : n < k) {s s₂ s' : SurfPos} (h_ssl : SSLComments s s₂)
    (h_entries : SBlockMapEntries k s₂ s') : SBlockNode n .blockIn s s' :=
  nestedBlockMap (Nat.le_of_lt hlt) h_ssl h_entries

/-! ## §5 The price

Tightening `m` means giving the two collection constructors a FLOOR on their
entries' width.  Written honestly the floor is `n < E` for a mapping and for a
block-in sequence, and `n ≤ E` for a block-out one — the `-1` the spec spends on
seq-spaces, and the reason `?⏎- a` is legal at all.  Both floors are false at
the root, whose spec index is `-1` and whose Lean index is `0`; so the root
needs an index this encoding does not have, and the tightening is a re-indexing
of `SBlockNode` (`n_lean = n_spec + 1` uniformly — the convention `[198]`'s own
docstring already states and these three constructors do not follow), not a
side condition on four call sites. -/

/-- The floors, as they would have to read. -/
private def widthFloor (n : Nat) (c : YamlContext) : Nat :=
  match c with
  | .blockOut => n
  | _ => n + 1

/-- They admit the equal-width landing's honest twin … -/
example (n k : Nat) (h : n < k) : widthFloor n .blockIn ≤ k := by
  simp [widthFloor]; omega
/-- … and refuse the landing itself, which is the point … -/
example (n : Nat) : ¬ (widthFloor n .blockIn ≤ n) := by simp [widthFloor]
/-- … and they keep the seq-spaces key, whose `-` is at the `?`'s own column … -/
example (n : Nat) : widthFloor n .blockOut ≤ n := by simp [widthFloor]
/-- … while the ROOT falls to the same refusal as the over-approximation, being
    indexed `0` where the spec indexes it `-1`. -/
example : ¬ (widthFloor 0 .blockIn ≤ 0) := by simp [widthFloor]

end L4YAML.Tests.Guards.BlockCollectionWidthFloor
