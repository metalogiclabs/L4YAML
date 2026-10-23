/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Production.Acceptance.Quoted

@[expose] public section Blanket

/-! # Acceptance (scanner converse) for block scalars

    The inverse of `scanBlockScalar_prod`, modulo `[162] c-b-block-header` (a separate
    hypothesis, `BlockHeaderOk`) and the content indent `n` (explicit, or the scanner's
    auto-detection — a state-side hypothesis).  `SLLiteralContent n` is STRICTLY wider
    than the scanner; refuters of the bare converse:
    * `|⏎  a⏎ b` — `[171]` at n = 1 derives both lines, the scanner detects 2 and stops
      at ` b`; hence `n` is pinned to the detected indent.
    * `|⏎a⏎---` — `[171]` at n = 0 derives `---`, the scanner stops at the document
      marker (`NotDocMarker` per content line).
    * `|⏎ a⏎# c` — `[169] l-trail-comments` is NOT consumed: the scanner stops before `#`.
    * `|x`, `|#c`, `|--` — `[162]` junk / unseparated comment / repeated indicator
      (`expectedNewline`).
    * `|⏎ a⏎  b⏎→c` — a tab where `s-indent(n)` is required (`tabInIndentation`). -/

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Grammar

/-! ## §1 `[63] s-indent` and one line of content -/

/-- `consumeExactSpaces` reads exactly an `SIndent n`. -/
lemma consumeExactSpaces_accepts {n : Nat} {sp sp' : SurfPos} (h : SIndent n sp sp') :
    ∀ sc : ScannerState, ScannerSurfCorr sc sp →
      ∃ sc', consumeExactSpaces sc n = (n, sc') ∧ ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | zero s => intro sc hcorr; exact ⟨sc, rfl, hcorr, Keeps.refl sc⟩
  | succ n rest col s' _ ih =>
    intro sc hcorr
    have hpk := (peek_of_corr hcorr).1
    obtain ⟨sc', heq, hc', hk⟩ := ih sc.advance (advance_corr hcorr (by decide) (by decide))
    refine ⟨sc', ?_, hc', (keeps_advance sc).trans hk⟩
    simp [consumeExactSpaces, hpk, heq]

/-- The characters `collectLineContentLoop` consumes: `[27] nb-char` as the scanner reads
    it (printable, not a break, not the BOM). -/
def LineCharOk (c : Char) : Prop :=
  isLineBreakBool c = false ∧ isPrintableBool c = true ∧ c ≠ '\uFEFF'

lemma lineCharOk_cond {c : Char} (h : LineCharOk c) :
    (isLineBreakBool c || !isPrintableBool c || c == '\uFEFF') = false := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [h1, h2, h3]

lemma not_lineCharOk_cond {c : Char} (h : ¬ LineCharOk c) :
    (isLineBreakBool c || !isPrintableBool c || c == '\uFEFF') = true := by
  unfold LineCharOk at h
  by_cases h1 : isLineBreakBool c = false
  · by_cases h2 : isPrintableBool c = true
    · have h3 : c = '\uFEFF' := by
        by_cases h3 : c = '\uFEFF'
        · exact h3
        · exact absurd ⟨h1, h2, h3⟩ h
      simp [h3]
    · simp [Bool.not_eq_true] at h2; simp [h2]
  · simp [Bool.not_eq_false] at h1; simp [h1]

/-- `collectLineContentLoop` reads a maximal `LineCharOk` run. -/
lemma collectLineContentLoop_accepts {sp sp' : SurfPos} (h : GStar (GChar LineCharOk) sp sp')
    (hmax : ∀ c, sp'.chars.head? = some c → ¬ LineCharOk c) :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat),
      ScannerSurfCorr sc sp → sp.chars.length ≤ fuel →
      ∃ sc' content', collectLineContentLoop sc content fuel = (content', sc') ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | nil s =>
    intro sc content fuel hcorr _
    refine ⟨sc, content, ?_, hcorr, Keeps.refl sc⟩
    cases fuel with
    | zero => rfl
    | succ f =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp [collectLineContentLoop, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        simp [collectLineContentLoop, hpk, not_lineCharOk_cond (hmax c rfl)]
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hnl : c ≠ '\n' := by intro e; subst e; exact absurd hc.1 (by decide)
        have hcr : c ≠ '\r' := by intro e; subst e; exact absurd hc.1 (by decide)
        obtain ⟨sc', content', heq, hc', hk⟩ :=
          ih hmax sc.advance (content.push c) f (advance_corr hcorr hnl hcr)
            (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        refine ⟨sc', content', ?_, hc', (keeps_advance sc).trans hk⟩
        simp [collectLineContentLoop, hpk, lineCharOk_cond hc, heq]

end L4YAML.Proofs.Acceptance
