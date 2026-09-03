/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Scalars

/-! # Reading-index lifts for scalar tokens and landing runs (DOCS item 45)

The flow stack carries a reading index `n` (item 44), and the accumulation's
evidence producers all conclude at 0.  This satellite is the leaf evidence
that lets item 46 thread a NONZERO index without reworking the deep scan-loop
inductions:

* **The landing split** (`gstar_white_take_sIndent`): the whites a
  break-crossing lands on either open with `[63] s-indent(n)` — `n` spaces,
  the rest `[66] s-separate-in-line` — or they under-run, and the under-run is
  LOCATED (`WhiteRunUnderRun`): `j < n` spaces followed by the run's end or a
  tab.  This is `gstar_white_sIndent_or_tab`'s question asked at a GIVEN `n`
  instead of an existential one, and it is the whole content of
  `[69] s-flow-line-prefix(n)` on a landing line.

* **The scalar lifts** (`SCDoubleQuoted_at` / `SCSingleQuoted_at` /
  `SNsPlain_at`): a scalar token's reading at 0 is a reading at EVERY `n`
  unless the derivation crossed a line — the single-line constructors bind
  their index without constraining it, so the lift is the same derivation
  re-tagged, and the multi-line case is returned as a located witness
  (`*Crossed`: the first line's own content, then the break) rather than
  generalized.  Lift the derivation, not the induction (Reflection 671): the
  scan-loop `_prod` chains stay at 0 untouched.

  The quoted lifts convert the CONTEXT freely (`[110]`/`[121]` read the same
  body classes in every context, so `.blockIn` evidence serves a `.flowOut`
  slot); the plain lift keeps its context — `[127] ns-plain-safe(c)` makes a
  plain scalar's characters context-sensitive, so only the index moves.

What stays at 0 after this file: multi-line scalar tokens (the `*Crossed`
witnesses) — item 46 collapses those at a nonzero index, and a later item can
narrow further by re-deriving their readings at `n` from the scanner's
per-line checks.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.FlowIndexLift

open L4YAML.Surface

/-! ## §1 The landing split at a given index -/

/-- The located under-run: the run opens with `j < n` spaces and then either
    ends or hits a tab — the two ways a landing line fails to supply
    `[63] s-indent(n)`. -/
def WhiteRunUnderRun (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ j sx, j < n ∧ SIndent j s sx ∧ GStar SSWhite sx s' ∧
    (sx = s' ∨ sx.chars.head? = some '\t')

/-- Split a white run at a GIVEN `n`: `s-indent(n)` plus residual whites, or
    the located under-run. -/
lemma gstar_white_take_sIndent (n : Nat) {s s' : SurfPos}
    (h : GStar SSWhite s s') :
    (∃ sx, SIndent n s sx ∧ GStar SSWhite sx s') ∨ WhiteRunUnderRun n s s' := by
  induction n generalizing s with
  | zero => exact Or.inl ⟨s, SIndent.zero s, h⟩
  | succ n ih =>
    cases h with
    | nil => exact Or.inr ⟨0, _, by omega, SIndent.zero _, GStar.nil _, Or.inl rfl⟩
    | cons _ s₂ s₃ hw hrest =>
      cases hw with
      | space rest col =>
        rcases ih hrest with ⟨sx, hind, hws⟩ | ⟨j, sx, hj, hind, hws, hend⟩
        · exact Or.inl ⟨sx, SIndent.succ n rest col sx hind, hws⟩
        · exact Or.inr ⟨j + 1, sx, by omega, SIndent.succ j rest col sx hind, hws, hend⟩
      | tab rest col =>
        exact Or.inr ⟨0, ⟨'\t' :: rest, col⟩, by omega, SIndent.zero _,
          GStar.cons _ _ _ (SSWhite.tab rest col) hrest, Or.inr rfl⟩

/-- The clean split, packaged as the line prefix `[69]` wants. -/
lemma gstar_white_flowLinePrefix_or_underRun (n : Nat) {s s' : SurfPos}
    (h : GStar SSWhite s s') :
    SFlowLinePrefix n s s' ∨ WhiteRunUnderRun n s s' := by
  rcases gstar_white_take_sIndent n h with ⟨sx, hind, hws⟩ | hur
  · refine Or.inl (SFlowLinePrefix.mk n s sx s' hind ?_)
    match hws with
    | GStar.nil _ => exact GOpt.none _
    | GStar.cons a b c hfirst hrest =>
      exact GOpt.some a c (SSeparateInLine.whites a c (GPlus.mk a b c hfirst hrest))
  · exact Or.inr hur

/-! ## §2 The scalar lifts -/

/-- A double-quoted body crossed a line: the first line's content, then
    `[113] s-double-break` (flow fold or escaped break). -/
def DoubleQuotedCrossed (s : SurfPos) : Prop :=
  ∃ s₁ sa sb, GLit '"' s s₁ ∧ SNbDoubleOneLine s₁ sa ∧ SSDoubleBreak 0 sa sb

/-- A single-quoted body crossed a line. -/
def SingleQuotedCrossed (s : SurfPos) : Prop :=
  ∃ s₁ sa sb, GLit '\'' s s₁ ∧ SNbSingleOneLine s₁ sa ∧ SBBreak sa sb

/-- A plain scalar crossed a line: its first line, then
    `[134] s-ns-plain-next-line`. -/
def PlainCrossed (s : SurfPos) : Prop :=
  ∃ (c : L4YAML.YamlContext) (sa sb : SurfPos),
    SNsPlainOneLine c s sa ∧ SSNsPlainNextLine 0 c sa sb

/-- One-line double-quoted body text reads at every index and context. -/
private lemma doubleText_of_oneLine (n : Nat) (c : L4YAML.YamlContext)
    {s₁ s₂ : SurfPos} (h : SNbDoubleOneLine s₁ s₂) : SNbDoubleText n c s₁ s₂ := by
  cases c <;> first
    | exact h
    | exact SNbDoubleMultiLine.single n s₁ s₂ h

/-- Read a multi-line double-quoted body back to one line, or the crossing. -/
private lemma doubleMulti_cases {s₁ s₂ : SurfPos}
    (h : SNbDoubleMultiLine 0 s₁ s₂) :
    SNbDoubleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbDoubleOneLine s₁ sa ∧ SSDoubleBreak 0 sa sb := by
  cases h with
  | single _ _ hl => exact Or.inl hl
  | multi _ _ _ _ _ hl hb _ => exact Or.inr ⟨_, _, hl, hb⟩

/-- Read a double-quoted body back to one line, or the crossing. -/
private lemma doubleText_cases {c : L4YAML.YamlContext} {s₁ s₂ : SurfPos}
    (h : SNbDoubleText 0 c s₁ s₂) :
    SNbDoubleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbDoubleOneLine s₁ sa ∧ SSDoubleBreak 0 sa sb := by
  cases c <;> first
    | exact Or.inl h
    | exact doubleMulti_cases h

/-- **The double-quoted lift**: a reading at 0 in any context is a reading at
    every `n` in every context, unless the body crossed a line. -/
lemma SCDoubleQuoted_at (n : Nat) (c' : L4YAML.YamlContext)
    {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted 0 c s s') :
    SCDoubleQuoted n c' s s' ∨ DoubleQuotedCrossed s := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases doubleText_cases hbody with hone | ⟨sa, sb, hl, hb⟩
    · exact Or.inl (SCDoubleQuoted.mk n c' _ _ _ _ hq1
        (doubleText_of_oneLine n c' hone) hq2)
    · exact Or.inr ⟨_, sa, sb, hq1, hl, hb⟩

/-- One-line single-quoted body text reads at every index and context. -/
private lemma singleText_of_oneLine (n : Nat) (c : L4YAML.YamlContext)
    {s₁ s₂ : SurfPos} (h : SNbSingleOneLine s₁ s₂) : SNbSingleText n c s₁ s₂ := by
  cases c <;> first
    | exact h
    | exact SNbSingleMultiLine.single n s₁ s₂ h

/-- Read a multi-line single-quoted body back to one line, or the crossing. -/
private lemma singleMulti_cases {s₁ s₂ : SurfPos}
    (h : SNbSingleMultiLine 0 s₁ s₂) :
    SNbSingleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbSingleOneLine s₁ sa ∧ SBBreak sa sb := by
  cases h with
  | single _ _ hl => exact Or.inl hl
  | multi _ _ _ _ _ _ hl hb _ _ _ => exact Or.inr ⟨_, _, hl, hb⟩

/-- Read a single-quoted body back to one line, or the crossing. -/
private lemma singleText_cases {c : L4YAML.YamlContext} {s₁ s₂ : SurfPos}
    (h : SNbSingleText 0 c s₁ s₂) :
    SNbSingleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbSingleOneLine s₁ sa ∧ SBBreak sa sb := by
  cases c <;> first
    | exact Or.inl h
    | exact singleMulti_cases h

/-- **The single-quoted lift** (see `SCDoubleQuoted_at`). -/
lemma SCSingleQuoted_at (n : Nat) (c' : L4YAML.YamlContext)
    {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted 0 c s s') :
    SCSingleQuoted n c' s s' ∨ SingleQuotedCrossed s := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases singleText_cases hbody with hone | ⟨sa, sb, hl, hb⟩
    · exact Or.inl (SCSingleQuoted.mk n c' _ _ _ _ hq1
        (singleText_of_oneLine n c' hone) hq2)
    · exact Or.inr ⟨_, sa, sb, hq1, hl, hb⟩

/-- The multi-line half of the plain lift. -/
private lemma plainMulti_at (n : Nat) {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SNsPlainMultiLine 0 c s s') :
    SNsPlainMultiLine n c s s' ∨ PlainCrossed s := by
  cases h with
  | mk _ _ hone hnext =>
    cases hnext with
    | nil => exact Or.inl (SNsPlainMultiLine.mk n _ _ _ _ hone (GStar.nil _))
    | cons _ _ _ hn _ => exact Or.inr ⟨_, _, _, hone, hn⟩

/-- **The plain lift**: same context — `[127] ns-plain-safe(c)` makes the
    characters context-sensitive, so only the index moves. -/
lemma SNsPlain_at (n : Nat) {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SNsPlain 0 c s s') :
    SNsPlain n c s s' ∨ PlainCrossed s := by
  cases c <;> first
    | exact Or.inl h
    | exact plainMulti_at n h

end L4YAML.Proofs.FlowIndexLift
