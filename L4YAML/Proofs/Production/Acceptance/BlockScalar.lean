/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Production.Acceptance.Plain

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

/-- `consumeExactSpaces` asked for `n` but finding only `k < n` spaces reads exactly them. -/
lemma consumeExactSpaces_short {k : Nat} {sp sp' : SurfPos} (h : SIndent k sp sp') :
    ∀ (n : Nat) (sc : ScannerState), k < n → ScannerSurfCorr sc sp → sp'.chars.head? ≠ some ' ' →
      ∃ sc', consumeExactSpaces sc n = (k, sc') ∧ ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | zero s =>
    intro n sc hk hcorr hsp
    refine ⟨sc, ?_, hcorr, Keeps.refl sc⟩
    cases n with
    | zero => omega
    | succ m =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp [consumeExactSpaces, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        have hc : c ≠ ' ' := fun e => hsp (by simp [e])
        simp only [consumeExactSpaces, hpk]
        split
        · rename_i e; exact absurd (Option.some.inj e) hc
        · rfl
  | succ k rest col s' _ ih =>
    intro n sc hk hcorr hsp
    cases n with
    | zero => omega
    | succ m =>
      have hpk := (peek_of_corr hcorr).1
      obtain ⟨sc', heq, hc', hk'⟩ :=
        ih m sc.advance (by omega) (advance_corr hcorr (by decide) (by decide)) hsp
      refine ⟨sc', ?_, hc', (keeps_advance sc).trans hk'⟩
      simp [consumeExactSpaces, hpk, heq]

lemma atDocBoundary_false_of_corr {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hnd : NotDocMarker sp) : atDocumentBoundary sc = false := by
  simp [atDocumentBoundary, atDocumentStart_false_of_corr hcorr hnd,
    atDocumentEnd_false_of_corr hcorr hnd]

/-! ## §2 Content lines and the loop's stops -/

/-- One line `collectBlockScalarLoop` folds at indent `n` and continues past: a blank line
    (at most `n` spaces, then a break) or `s-indent(n)` + a maximal non-empty `LineCharOk`
    run + a break; never a document marker at column 0. -/
inductive BlockLineOk (n : Nat) : SurfPos → SurfPos → Prop where
  | blank (k : Nat) (s s₁ s' : SurfPos) :
      NotDocMarker s → k ≤ n → SIndent k s s₁ → SBBreakOk s₁ s' → BlockLineOk n s s'
  | content (s s₁ s₂ s' : SurfPos) :
      NotDocMarker s → SIndent n s s₁ → GPlus (GChar LineCharOk) s₁ s₂ →
      SBBreakOk s₂ s' → BlockLineOk n s s'

/-- Where `collectBlockScalarLoop` stops at indent `n`, and where it lands: end of input
    after a partial indent or a last line; a less-indented line (landing at its start — a
    tab there is the scanner's `tabInIndentation`); a non-`LineCharOk`, non-break
    character after a line. -/
inductive BlockStopOk (n : Nat) : SurfPos → SurfPos → Prop where
  | eofShort (k : Nat) (s s' : SurfPos) :
      NotDocMarker s → k < n → SIndent k s s' → s'.chars = [] → BlockStopOk n s s'
  | eofLine (s s₁ s' : SurfPos) :
      NotDocMarker s → SIndent n s s₁ → GStar (GChar LineCharOk) s₁ s' → s'.chars = [] →
      BlockStopOk n s s'
  | outdent (k : Nat) (s s₁ : SurfPos) (c : Char) :
      NotDocMarker s → k < n → SIndent k s s₁ → s₁.chars.head? = some c →
      isLineBreakBool c = false → c ≠ ' ' → c ≠ '\t' → BlockStopOk n s s
  | badChar (s s₁ s' : SurfPos) (c : Char) :
      NotDocMarker s → SIndent n s s₁ → GStar (GChar LineCharOk) s₁ s' →
      s'.chars.head? = some c → isLineBreakBool c = false → ¬ LineCharOk c →
      BlockStopOk n s s'

lemma SIndent.length_le {k : Nat} {s s' : SurfPos} (h : SIndent k s s') :
    s'.chars.length + k = s.chars.length := by
  induction h with
  | zero s => rfl
  | succ k rest col s' _ ih => dsimp only at ih ⊢; simp only [List.length_cons]; omega

lemma GStar_lineChar_length {s s' : SurfPos} (h : GStar (GChar LineCharOk) s s') :
    s'.chars.length ≤ s.chars.length := by
  induction h with
  | nil s => exact Nat.le_refl _
  | cons s₁ s₂ s₃ hstep _ ih => cases hstep; simp only [List.length_cons] at ih ⊢; omega

lemma GPlus_lineChar_length_lt {s s' : SurfPos} (h : GPlus (GChar LineCharOk) s s') :
    s'.chars.length < s.chars.length := by
  cases h with
  | mk _ _ hstep hrest => cases hstep; have := GStar_lineChar_length hrest; simp only [List.length_cons] at this ⊢; omega

/-- The stop of `collectBlockScalarLoop` on a `BlockStopOk` landing (one iteration). -/
lemma collectBlockScalarLoop_stops (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hstop : BlockStopOk n sp sp') (hcorr : ScannerSurfCorr sc sp) (raw : String)
    (fuel ie : Nat) (hie : sc.inputEnd = ie) :
    ScannerSurfCorr (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 sp' ∧
      Keeps sc (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 := by
  cases hstop with
  | eofShort k s s' hnd hk hind heof =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_short hind n sc hk hcorr (by simp [heof])
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    obtain ⟨chars, col⟩ := sp'
    simp only at heof; subst heof
    have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₁ := by
      simp [collectBlockScalarLoop, hdb, heq, peek_none_of_corr hc₁]
    rw [hres]; exact ⟨hc₁, hk₁⟩
  | eofLine s s₁ s' hnd hind hrun heof =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_accepts hind sc hcorr
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    obtain ⟨chars, col⟩ := sp'
    simp only at heof; subst heof
    cases hrun with
    | nil _ =>
      have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₁ := by
        simp [collectBlockScalarLoop, hdb, heq, peek_none_of_corr hc₁]
      rw [hres]; exact ⟨hc₁, hk₁⟩
    | cons _ s₂ _ hstep hrest =>
      cases hstep with
      | mk c rest col₁ hc =>
        have hmax : ∀ c, (⟨[], col⟩ : SurfPos).chars.head? = some c → ¬ LineCharOk c := by
          intro c hc; simp at hc
        obtain ⟨sc₂, content, heq₂, hc₂, hk₂⟩ :=
          collectLineContentLoop_accepts (GStar.cons _ _ _ (GChar.mk c rest col₁ hc) hrest) hmax
            sc₁ "" (ie - sc₁.offset + 1) hc₁
            (by have := fuel_of_corr hc₁; rw [hk₁.2.1, hie] at this; omega)
        have hpk := (peek_of_corr hc₁).1
        have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₂ := by
          simp [collectBlockScalarLoop, hdb, heq, hpk, hc.1, heq₂, peek_none_of_corr hc₂]
        rw [hres]; exact ⟨hc₂, hk₁.trans hk₂⟩
  | outdent k s s₁ c hnd hk hind hhead hnb hsp htab =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_short hind n sc hk hcorr (by simp [hhead, hsp])
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    obtain ⟨chars, col⟩ := s₁
    cases chars with
    | nil => simp at hhead
    | cons d tl =>
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hpk := (peek_of_corr hc₁).1
      have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc := by
        simp [collectBlockScalarLoop, hdb, heq, hpk, hnb, hk]
      rw [hres]; exact ⟨hcorr, Keeps.refl sc⟩
  | badChar s s₁ s' c hnd hind hrun hhead hnb hbad =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_accepts hind sc hcorr
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    have hmax : ∀ d, sp'.chars.head? = some d → ¬ LineCharOk d := by
      intro d hd; rw [hhead] at hd; cases hd; exact hbad
    obtain ⟨sc₂, content, heq₂, hc₂, hk₂⟩ :=
      collectLineContentLoop_accepts hrun hmax sc₁ "" (ie - sc₁.offset + 1) hc₁
        (by have := fuel_of_corr hc₁; rw [hk₁.2.1, hie] at this; omega)
    obtain ⟨chars, col⟩ := sp'
    cases chars with
    | nil => simp at hhead
    | cons d tl =>
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hpk₂ := (peek_of_corr hc₂).1
      cases hrun with
      | nil _ =>
        have hpk := (peek_of_corr hc₁).1
        have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₂ := by
          simp [collectBlockScalarLoop, hdb, heq, hpk, hnb, heq₂, hpk₂]
        rw [hres]; exact ⟨hc₂, hk₁.trans hk₂⟩
      | cons _ s₂ _ hstep hrest =>
        cases hstep with
        | mk e rest col₁ he =>
          have hpk := (peek_of_corr hc₁).1
          have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₂ := by
            simp [collectBlockScalarLoop, hdb, heq, hpk, he.1, heq₂, hpk₂, hnb]
          rw [hres]; exact ⟨hc₂, hk₁.trans hk₂⟩

lemma BlockLineOk.length_lt {n : Nat} {s s' : SurfPos} (h : BlockLineOk n s s') :
    s'.chars.length < s.chars.length := by
  cases h with
  | blank k _ s₁ _ _ _ hind hb => have := SIndent.length_le hind; have := hb.length_lt; omega
  | content _ s₁ s₂ _ _ hind hrun hb =>
    have := SIndent.length_le hind; have := GPlus_lineChar_length_lt hrun; have := hb.length_lt; omega

/-- One `BlockLineOk` line is folded and the loop continues on the rest. -/
lemma collectBlockScalarLoop_line_step (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hline : BlockLineOk n sp sp') (hcorr : ScannerSurfCorr sc sp) (raw : String)
    (fuel ie : Nat) (hie : sc.inputEnd = ie) :
    ∃ sc' raw', ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧
      collectBlockScalarLoop sc raw (fuel + 1) n ie = collectBlockScalarLoop sc' raw' fuel n ie := by
  have hdb := atDocBoundary_false_of_corr hcorr (by cases hline <;> assumption)
  cases hline with
  | blank k s s₁ s' hnd hk hind hb =>
    obtain ⟨c, rest, hs₁, hlb⟩ := hb.head
    have hns : s₁.chars.head? ≠ some ' ' := by
      rw [hs₁]; intro e; simp at e; subst e; exact absurd hlb (by decide)
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ : ∃ sc₁, consumeExactSpaces sc n = (k, sc₁) ∧
        ScannerSurfCorr sc₁ s₁ ∧ Keeps sc sc₁ := by
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · exact consumeExactSpaces_short hind n sc hlt hcorr hns
      · subst heq; exact consumeExactSpaces_accepts hind sc hcorr
    obtain ⟨chars, col⟩ := s₁
    simp only at hs₁; subst hs₁
    have hpk := (peek_of_corr hc₁).1
    obtain ⟨hc₂, hk₂⟩ := consumeNewline_accepts sc₁ hb hc₁
    refine ⟨consumeNewline sc₁, raw.push '\n', hc₂, hk₁.trans hk₂, ?_⟩
    simp [collectBlockScalarLoop, hdb, heq, hpk, hlb]
  | content s s₁ s₂ s' hnd hind hrun hb =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_accepts hind sc hcorr
    obtain ⟨c, rest, hs₂, hlb⟩ := hb.head
    have hmax : ∀ d, s₂.chars.head? = some d → ¬ LineCharOk d := by
      intro d hd; rw [hs₂] at hd; cases hd; intro h; rw [h.1] at hlb; cases hlb
    obtain ⟨sc₂, content, heq₂, hc₂, hk₂⟩ :=
      collectLineContentLoop_accepts (GPlus.toGStar hrun) hmax sc₁ "" (ie - sc₁.offset + 1) hc₁
        (by have := fuel_of_corr hc₁; rw [hk₁.2.1, hie] at this; omega)
    cases hrun with
    | mk _ _ hstep hrest =>
      cases hstep with
      | mk e rest₁ col₁ he =>
        have hpk := (peek_of_corr hc₁).1
        obtain ⟨chars, col⟩ := s₂
        simp only at hs₂; subst hs₂
        have hpk₂ := (peek_of_corr hc₂).1
        obtain ⟨hc₃, hk₃⟩ := consumeNewline_accepts sc₂ hb hc₂
        refine ⟨consumeNewline sc₂, (raw ++ content).push '\n', hc₃, (hk₁.trans hk₂).trans hk₃, ?_⟩
        simp [collectBlockScalarLoop, hdb, heq, hpk, he.1, heq₂, hpk₂, hlb]

/-- Converse of `collectBlockScalarLoop_literal_prod`: `BlockLineOk n` lines then a
    `BlockStopOk n` stop are read, landing at the stop's position. -/
lemma collectBlockScalarLoop_accepts {n : Nat} {sp sp' : SurfPos}
    (hlines : GStar (BlockLineOk n) sp sp') :
    ∀ (sc : ScannerState) (raw : String) (fuel ie : Nat) (sp'' : SurfPos),
      ScannerSurfCorr sc sp → sc.inputEnd = ie → BlockStopOk n sp' sp'' →
      sp.chars.length < fuel →
      ScannerSurfCorr (collectBlockScalarLoop sc raw fuel n ie).2 sp'' ∧
        Keeps sc (collectBlockScalarLoop sc raw fuel n ie).2 := by
  induction hlines with
  | nil s =>
    intro sc raw fuel ie sp'' hcorr hie hstop hfuel
    cases fuel with
    | zero => omega
    | succ f => exact collectBlockScalarLoop_stops sc hstop hcorr raw f ie hie
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc raw fuel ie sp'' hcorr hie hstop hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      obtain ⟨sc', raw', hc', hk', heq⟩ := collectBlockScalarLoop_line_step sc hstep hcorr raw f ie hie
      have hlt := hstep.length_lt
      obtain ⟨h1, h2⟩ := ih sc' raw' f ie sp'' hc' (by rw [hk'.2.1, hie]) hstop (by omega)
      rw [heq]; exact ⟨h1, hk'.trans h2⟩

end L4YAML.Proofs.Acceptance
