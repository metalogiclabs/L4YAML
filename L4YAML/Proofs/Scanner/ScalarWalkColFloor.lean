/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Production.ScalarProduction

/-! # The scalar walks' cross-line column floor (DOCS item 122)

The three multi-line content walks are the only scans that can leave a LIVE
simple-key candidate saved on an earlier line than the cursor's — the plain
walk and the two quoted walks save at their start and then fold continuation
lines.  Item 121's `?`-line column bound (U1) needs exactly one fact about
each: **a walk that ends on a line other than its entry line ends with its
column strictly past `currentIndent`.**  Each walk enforces this itself:

* the BLOCK plain walk's continuation gate is its `contentIndent` parameter,
  which `scanPlainScalar` sets to `(max 0 (currentIndent + 1)).toNat` — every
  absorbed landing already clears the block floor STRICTLY, with no premise
  about the walk's own start column;
* both quoted folds throw `underIndentedScalar` on a landing at or left of
  the `currentIndent` parameter (`[69] s-flow-line-prefix(n)`'s `s-indent(n)`,
  §8.1), in BOTH contexts, so an `.ok` exit off the entry line sits strictly
  past it.

Stated per loop as a line-or-floor disjunction (the exit is on the entry
line, or its column clears the floor) and exported per scan in the form the
dispatch layer consumes.  The flow-side twin — a dispatched token inside a
flow sits past the floor — is `FlowIndentStable.structural_none_col_gt_of_inFlow`
already. -/

set_option autoImplicit false

namespace L4YAML.Proofs.ScalarWalkColFloor

open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarProduction

/-! ## §1  Column monotonicity of the walks' same-line helpers -/

/-- A non-break `advance` spends exactly one column. -/
private lemma advance_col_succ_of_peek {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false) :
    s.advance.col = s.col + 1 := by
  unfold ScannerState.peek? at hpk
  split at hpk
  · rename_i hlt
    have hc : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := Option.some.inj hpk
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnb
    exact advance_col_non_newline s hlt (by rw [hc]; simpa using hnb.1)
      (by rw [hc]; simpa using hnb.2)
  · cases hpk

/-- `s-white` is not `b-char`: the separation walk moves the column only. -/
private lemma skipWhitespaceLoop_col_ge (s : ScannerState) (fuel : Nat) :
    s.col ≤ (skipWhitespaceLoop s fuel).col := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    unfold skipWhitespaceLoop
    split
    · rename_i c hpk
      split
      · rename_i hws
        have hnb : isLineBreakBool c = false := by
          simp only [isWhiteSpaceBool, isSpaceBool, isTabBool, Bool.or_eq_true,
            beq_iff_eq] at hws
          rcases hws with rfl | rfl <;> decide
        calc s.col ≤ s.advance.col := by rw [advance_col_succ_of_peek hpk hnb]; omega
          _ ≤ _ := ih s.advance
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma skipWhitespace_col_ge (s : ScannerState) :
    s.col ≤ (skipWhitespace s).col :=
  skipWhitespaceLoop_col_ge s _

/-- `ns-hex-digit` is not `b-char` either: the escape body moves the column
    only (`collectHexDigitsLoop_line`'s column half). -/
private lemma collectHexDigitsLoop_col_ge (s : ScannerState) (hex : String) (n : Nat) :
    s.col ≤ (collectHexDigitsLoop s hex n).2.col := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; exact Nat.le_refl _
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · rename_i c hp
      split
      · rename_i hhex
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · exfalso
            simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
              Bool.or_eq_true, beq_iff_eq] at hlb
            rcases hlb with rfl | rfl <;> exact absurd hhex (by decide)
        calc s.col ≤ s.advance.col := by rw [advance_col_succ_of_peek hp hnb]; omega
          _ ≤ _ := ih s.advance (hex.push c)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma parseHexEscape_col_ge {s : ScannerState} {n : Nat} {ch : Char}
    {s' : ScannerState} (hok : parseHexEscape s n = .ok (ch, s')) :
    s.col ≤ s'.col := by
  unfold parseHexEscape at hok
  dsimp only [] at hok
  split at hok
  · simp at hok
  · split at hok
    · obtain ⟨-, rfl⟩ := hok
      exact collectHexDigitsLoop_col_ge s "" n
    · simp at hok

/-- `[62] c-ns-esc-char` admits no break, so the escape moves the column only
    (`processEscape_line`'s column half; the ESCAPED break is not routed here). -/
private lemma processEscape_col_ge {s : ScannerState} {ch : Char} {s' : ScannerState}
    (hproc : processEscape s = .ok (ch, s')) : s.col ≤ s'.col := by
  unfold processEscape at hproc
  split at hproc
  · simp at hproc
  · rename_i c_esc hpeek
    dsimp only [] at hproc
    split at hproc <;> (first
      | (obtain ⟨-, rfl⟩ := hproc; try subst_vars
         rw [advance_col_succ_of_peek hpeek (by decide)]; omega)
      | skip)
    · -- 'x': hex escape (n = 2)
      try subst_vars
      calc s.col ≤ s.advance.col := by
            rw [advance_col_succ_of_peek hpeek (by decide)]; omega
        _ ≤ _ := parseHexEscape_col_ge hproc
    · -- 'u': hex escape (n = 4)
      try subst_vars
      calc s.col ≤ s.advance.col := by
            rw [advance_col_succ_of_peek hpeek (by decide)]; omega
        _ ≤ _ := parseHexEscape_col_ge hproc
    · -- 'U': hex escape (n = 8)
      try subst_vars
      calc s.col ≤ s.advance.col := by
            rw [advance_col_succ_of_peek hpeek (by decide)]; omega
        _ ≤ _ := parseHexEscape_col_ge hproc
    · simp at hproc

/-- **The block fold's landing clears the walk's own gate**: a `some` return
    of `collectPlainScalar_handleBlockLineBreak` sits at or right of
    `contentIndent` — the under-indent test is `[63] s-indent`'s, and the
    `s-separate-in-line` run after it only moves right. -/
private lemma handleBlockLineBreak_col_ge {s s' : ScannerState}
    {content content' : String} {ci ie : Nat}
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s')) :
    ci ≤ s'.col := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hcol
    split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_trans (Nat.le_of_not_lt hcol) (skipWhitespace_col_ge _)

/-- The terminator results hand back the walk's CURRENT state. -/
private lemma terminates?_state {c : Char} {s : ScannerState}
    {content spaces : String} {inFlow : Bool} {r : PlainScalarResult}
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some r) :
    r.state = s := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; subst h; rfl
  · split at h
    · simp only [] at h
      split at h <;> split at h <;> first
        | (injection h with h; subst h; rfl)
        | cases h
    · split at h
      · injection h with h; subst h; rfl
      · split at h
        · injection h with h; subst h; rfl
        · cases h

/-! ## §2  The walks, as line-or-floor disjunctions -/

/-- **The BLOCK plain walk exits on its entry line or past its gate.**  Every
    recursive step either spends a column on a non-break character or lands a
    fold at `contentIndent` or deeper; the stop paths return a state some
    earlier step certified. -/
private lemma collectPlainScalarLoop_line_or_floor (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie l₀ : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    (s.line = l₀ ∨ ci ≤ s.col) →
    r.state.line = l₀ ∨ ci ≤ r.state.col := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie l₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    exact hinv
  | succ fuel' ih =>
    intro s content spaces ci ie l₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq
      exact hinv
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        injection hok with h_eq; subst h_eq
        exact (terminates?_state hterm') ▸ hinv
      · split at hok
        · -- a break, block context
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact hinv
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq
                exact hinv
              · dsimp only [] at hok
                generalize h_loop :
                  collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq
                    exact hinv
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" ci ie l₀ _ h_loop
                      (Or.inr (handleBlockLineBreak_col_ge hblk))
                | error e => simp at hok
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          have hstep : s.advance.line = l₀ ∨ ci ≤ s.advance.col := by
            rcases hinv with h | h
            · exact Or.inl ((advance_preserves_line_of_ne_break s c hpk
                (by intro hc; rw [hc] at hnb; cases hnb)
                (by intro hc; rw [hc] at hnb; cases hnb)).trans h)
            · exact Or.inr (by rw [advance_col_succ_of_peek hpk hnb]; omega)
          split at hok
          · exact ih s.advance content _ ci ie l₀ r hok hstep
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact hinv
            · exact ih s.advance _ "" ci ie l₀ r hok hstep

/-- **The double-quoted walk exits on its entry line or past the floor.**  The
    two folds re-establish the strict bound through their own
    `underIndentedScalar` gate; everything else is same-line. -/
private lemma collectDoubleQuotedLoop_line_or_floor (sc : ScannerState)
    (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd protectedLen : Nat) (l₀ : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd protectedLen = .ok (result_content, s'))
    (hinv : sc.line = l₀ ∨ currentIndent < (sc.col : Int)) :
    s'.line = l₀ ∨ currentIndent < (s'.col : Int) := by
  induction fuel generalizing sc content protectedLen with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- closing quote
      rename_i _ hpeek
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      rcases hinv with h | h
      · exact Or.inl ((advance_preserves_line_of_ne_break sc '"' hpeek
          (by decide) (by decide)).trans h)
      · exact Or.inr (by rw [advance_col_succ_of_peek hpeek (by decide)]; push_cast; omega)
    · -- backslash
      rename_i _ hpeek
      have hstep : sc.advance.line = l₀ ∨ currentIndent < (sc.advance.col : Int) := by
        rcases hinv with h | h
        · exact Or.inl ((advance_preserves_line_of_ne_break sc '\\' hpeek
            (by decide) (by decide)).trans h)
        · exact Or.inr (by rw [advance_col_succ_of_peek hpeek (by decide)]; push_cast; omega)
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · -- escaped break: the landing runs through the fold's own gate
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · rename_i hcol_ok
                exact ih _ _ _ hok (Or.inr (by omega))
        · -- regular escape: same line, column only grows
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            refine ih _ _ _ hok ?_
            rcases hstep with h | h
            · exact Or.inl ((processEscape_line hproc).trans h)
            · exact Or.inr (by
                have := processEscape_col_ge hproc
                omega)
      · exact absurd hok (by simp)
    · -- regular character
      rename_i _opt c hne_dq hne_bs hpeek
      split at hok
      · -- line break: the fold's gate re-establishes the strict bound
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · rename_i hcol_ok
              exact ih _ _ _ hok (Or.inr (by omega))
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have hnb : isLineBreakBool c = false := by simpa using hne_lb
          refine ih _ _ _ hok ?_
          rcases hinv with h | h
          · exact Or.inl ((advance_preserves_line_of_ne_break sc c hpeek
              (by intro hc; rw [hc] at hnb; cases hnb)
              (by intro hc; rw [hc] at hnb; cases hnb)).trans h)
          · exact Or.inr (by rw [advance_col_succ_of_peek hpeek hnb]; push_cast; omega)

/-- `collectSingleQuotedLoop`'s twin of the above. -/
private lemma collectSingleQuotedLoop_line_or_floor (sc : ScannerState)
    (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd : Nat) (l₀ : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd = .ok (result_content, s'))
    (hinv : sc.line = l₀ ∨ currentIndent < (sc.col : Int)) :
    s'.line = l₀ ∨ currentIndent < (s'.col : Int) := by
  induction fuel generalizing sc content with
  | zero => simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- a quote: escaped pair, or the close
      rename_i _ hpeek
      have hstep : sc.advance.line = l₀ ∨ currentIndent < (sc.advance.col : Int) := by
        rcases hinv with h | h
        · exact Or.inl ((advance_preserves_line_of_ne_break sc '\'' hpeek
            (by decide) (by decide)).trans h)
        · exact Or.inr (by rw [advance_col_succ_of_peek hpeek (by decide)]; push_cast; omega)
      dsimp only [] at hok
      split at hok
      · -- escaped quote '': one more column
        rename_i hpeek2
        refine ih _ _ hok ?_
        rcases hstep with h | h
        · exact Or.inl ((advance_preserves_line_of_ne_break sc.advance '\'' hpeek2
            (by decide) (by decide)).trans h)
        · exact Or.inr (by rw [advance_col_succ_of_peek hpeek2 (by decide)]; push_cast; omega)
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        exact hstep
    · -- regular character
      rename_i _opt c hne_sq hpeek
      split at hok
      · -- line break: the fold's gate
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · rename_i hcol_ok
              exact ih _ _ hok (Or.inr (by omega))
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have hnb : isLineBreakBool c = false := by simpa using hne_lb
          refine ih _ _ hok ?_
          rcases hinv with h | h
          · exact Or.inl ((advance_preserves_line_of_ne_break sc c hpeek
              (by intro hc; rw [hc] at hnb; cases hnb)
              (by intro hc; rw [hc] at hnb; cases hnb)).trans h)
          · exact Or.inr (by rw [advance_col_succ_of_peek hpeek hnb]; push_cast; omega)

/-! ## §3  The per-scan exports: cross-line exit ⇒ strictly past the floor -/

/-- **A block-context plain scalar that ends off its entry line ends strictly
    past the block floor** — with no premise about its start column:
    `scanPlainScalar` gates continuation landings on
    `(max 0 (currentIndent + 1)).toNat` itself. -/
lemma scanPlainScalar_crossline_col_floor {s s' : ScannerState}
    (h_noflow : s.inFlow = false)
    (hok : scanPlainScalar s = .ok s')
    (h_ne : s'.line ≠ s.line) :
    s.currentIndent < (s'.col : Int) := by
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind, h_noflow, Bool.false_eq_true, ↓reduceIte] at hok
  split at hok
  · cases hok
  · rename_i r h_loop
    have h_eq := Except.ok.inj hok
    have h_line : s'.line = r.state.line := by rw [← h_eq]; rfl
    have h_col : s'.col = r.state.col := by rw [← h_eq]; rfl
    rcases collectPlainScalarLoop_line_or_floor _ s "" ""
        ((max 0 (s.currentIndent + 1)).toNat) s.inputEnd s.line r
        h_loop (Or.inl rfl) with h | h
    · exact absurd (h_line.trans h) h_ne
    · rw [h_col]; omega

/-- **A double-quoted scalar that ends off its entry line ends strictly past
    the block floor** (`[69] s-flow-line-prefix(n)`, both contexts). -/
lemma scanDoubleQuoted_crossline_col_floor {s s' : ScannerState}
    (h_pk : s.peek? = some '"')
    (hok : scanDoubleQuoted s = .ok s')
    (h_ne : s'.line ≠ s.line) :
    s.currentIndent < (s'.col : Int) := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    -- the trailing-content probe and the emit both leave the cursor alone
    have h_fields : s'.line = res.2.line ∧ s'.col = res.2.col := by
      split at hok
      · split at hok
        · cases hok
        · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
      · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
    rcases collectDoubleQuotedLoop_line_or_floor s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd 0 s.line h_loop
        (Or.inl (advance_preserves_line_of_ne_break s '"' h_pk
          (by decide) (by decide))) with h | h
    · exact absurd (h_fields.1.trans h) h_ne
    · rw [h_fields.2]; omega

/-- `scanSingleQuoted`'s twin. -/
lemma scanSingleQuoted_crossline_col_floor {s s' : ScannerState}
    (h_pk : s.peek? = some '\'')
    (hok : scanSingleQuoted s = .ok s')
    (h_ne : s'.line ≠ s.line) :
    s.currentIndent < (s'.col : Int) := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    have h_fields : s'.line = res.2.line ∧ s'.col = res.2.col := by
      split at hok
      · split at hok
        · cases hok
        · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
      · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
    rcases collectSingleQuotedLoop_line_or_floor s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd s.line h_loop
        (Or.inl (advance_preserves_line_of_ne_break s '\'' h_pk
          (by decide) (by decide))) with h | h
    · exact absurd (h_fields.1.trans h) h_ne
    · rw [h_fields.2]; omega

end L4YAML.Proofs.ScalarWalkColFloor
