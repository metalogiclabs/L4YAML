/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Scanner.PendingKeySound
public import L4YAML.Proofs.Scanner.StaleCursorFloor
public import L4YAML.Proofs.Scanner.ScalarWalkColFloor
public import L4YAML.Proofs.Scanner.LineOpenGuard
public import L4YAML.Proofs.Scanner.PropsRunLineCoupling
public import L4YAML.Proofs.Scanner.BlockScalarFlowGuard
public import L4YAML.Proofs.Scanner.FlowIndentStable
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Scanner.AliasTrailingContent
public import L4YAML.Proofs.Production.PreprocessProduction
public import L4YAML.Proofs.Scanner.ScanStrictCoupling

@[expose] public section Blanket

/-!
# The cursor floor, carried at the token level (DOCS item 339)

Item 338 proved `PendingKeySound.Sound` through every `scanNextToken` arm but
left one premise STARVED: after preprocessing, the cursor sits at or right of
the current indent (`PreprocessFloor`).  The unwind supplies it when an indent
check was pending; when none was, it is a fact about the cursor the carrier
did not hold.  This module carries it:

* `ColFloor.floor` — `needIndentCheck = false → currentIndent ≤ col`, in both
  contexts.  Inside flow the scanner refuses under-indented content
  (`underIndentedFlowContent` in `scanNextToken_dispatchStructural`,
  `underIndentedScalar` in the scalar loops), so a flow close that returns to
  block level inherits a floor that already holds.
* `ColFloor.key` / `ColFloor.stack` — every saved simple key (the live one and
  the ones stacked by flow openers) sits BEHIND the cursor, lexicographically
  on (line, col).  The `:` arm spends it: `scanValuePrepare` opens a block
  mapping at the KEY's column, and the floor after the `:` needs that column
  at or left of the cursor.  (`KeysBehindCursor` is the same fact on offsets;
  the push reads columns.)

`preprocessFloor` is the bridge to item 338's premise; `scanNextToken_colfloor`
carries the structure through one token so `StreamAccum` can thread both.
-/


namespace L4YAML.Proofs.ColFloor

open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.PreprocessIndentStable (currentIndent_of_indents_eq)

/-! ## §1  Cursor order -/

/-- The cursor of `s'` is at or after the cursor of `s`, lexicographically. -/
def Forward (s s' : ScannerState) : Prop :=
  s.line < s'.line ∨ (s'.line = s.line ∧ s.col ≤ s'.col)

/-- A saved position sits at or behind the cursor. -/
def Behind (p : YamlPos) (s : ScannerState) : Prop :=
  p.line < s.line ∨ (p.line = s.line ∧ p.col ≤ s.col)

lemma Forward.refl (s : ScannerState) : Forward s s := Or.inr ⟨rfl, Nat.le_refl _⟩

lemma Forward.trans {s t u : ScannerState} (h1 : Forward s t) (h2 : Forward t u) :
    Forward s u := by
  unfold Forward at *; omega

lemma Forward.of_same_line {s s' : ScannerState} (hl : s'.line = s.line) (hc : s.col ≤ s'.col) :
    Forward s s' := Or.inr ⟨hl, hc⟩

lemma Forward.of_fields {s s' : ScannerState} (hl : s'.line = s.line) (hc : s'.col = s.col) :
    Forward s s' := Or.inr ⟨hl, hc ▸ Nat.le_refl _⟩

lemma Forward.col_le_of_line_eq {s s' : ScannerState} (hf : Forward s s') (hl : s'.line = s.line) :
    s.col ≤ s'.col := by
  unfold Forward at hf; omega

lemma Behind.mono {p : YamlPos} {s s' : ScannerState} (h : Behind p s) (hf : Forward s s') :
    Behind p s' := by
  unfold Behind Forward at *; omega

lemma Behind.of_pos (s : ScannerState) : Behind s.currentPos s :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

lemma Forward.advance (s : ScannerState) : Forward s s.advance := by
  unfold Forward ScannerState.advance
  by_cases h : s.offset < s.inputEnd
  · simp only [h, ↓reduceIte]
    by_cases h1 : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true
    · simp [h1]
    · by_cases h2 : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\r') = true
      · simp [h1, h2]
      · simp [h1, h2]
  · simp [h]

lemma Forward.advanceNLoop (s : ScannerState) (n : Nat) : Forward s (s.advanceNLoop n) := by
  induction n generalizing s with
  | zero => exact Forward.refl s
  | succ n ih => exact (Forward.advance s).trans (ih s.advance)

lemma Forward.advanceN (s : ScannerState) (n : Nat) : Forward s (s.advanceN n) :=
  Forward.advanceNLoop s n

lemma Forward.emit (s : ScannerState) (t : YamlToken) : Forward s (s.emit t) :=
  Forward.of_fields rfl rfl

/-- One non-break character spends one column on its line. -/
lemma Forward.advance_of_nb {s : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hnb : isLineBreakBool c = false) : s.advance.line = s.line ∧ s.advance.col = s.col + 1 := by
  refine ⟨advance_preserves_line_of_ne_break s c hpk ?_ ?_,
    L4YAML.Proofs.ScalarWalkColFloor.advance_col_succ_of_peek hpk hnb⟩
  · rintro rfl; revert hnb; decide
  · rintro rfl; revert hnb; decide

/-! ## §2  The carrier -/

/-- **The cursor floor.** -/
structure ColFloor (s : ScannerState) : Prop where
  floor : s.needIndentCheck = false → s.currentIndent ≤ (s.col : Int)
  key : s.simpleKey.possible = true → Behind s.simpleKey.pos s
  stack : ∀ j (h : j < s.simpleKeyStack.size),
    s.simpleKeyStack[j].possible = true → Behind s.simpleKeyStack[j].pos s

/-- Transport along a step that keeps the keys and moves the cursor forward;
    the floor is the one obligation left to the caller. -/
lemma ColFloor.of_forward {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' where
  floor := hfloor
  key := by rw [hsk]; intro hp; exact (h.key hp).mono hf
  stack := by
    intro j hj hp
    simp only [hst] at hj hp ⊢
    exact (h.stack j hj hp).mono hf

/-- The same, with the live key cleared by the step. -/
lemma ColFloor.of_forward_cleared {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey.possible = false) (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' where
  floor := hfloor
  key := by intro hp; rw [hsk] at hp; cases hp
  stack := by
    intro j hj hp
    simp only [hst] at hj hp ⊢
    exact (h.stack j hj hp).mono hf

/-- Transport along a field touch-up that keeps the cursor, the indents, the
    key's `possible`/`pos` and the stack (the quoted arms' `endLine` write). -/
lemma ColFloor.of_touchup {s s' : ScannerState} (h : ColFloor s)
    (hnic : s'.needIndentCheck = s.needIndentCheck) (hind : s'.indents = s.indents)
    (hcol : s'.col = s.col) (hline : s'.line = s.line)
    (hp : s'.simpleKey.possible = s.simpleKey.possible) (hpos : s'.simpleKey.pos = s.simpleKey.pos)
    (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' where
  floor := by
    intro hn; rw [hnic] at hn
    rw [currentIndent_of_indents_eq hind, hcol]; exact h.floor hn
  key := by
    intro hk; rw [hp] at hk; rw [hpos]
    exact (h.key hk).mono (Forward.of_fields hline hcol)
  stack := by
    intro j hj hk
    simp only [hst] at hj hk ⊢
    exact (h.stack j hj hk).mono (Forward.of_fields hline hcol)

lemma ColFloor.of_forward_or {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey = s.simpleKey ∨ s'.simpleKey.possible = false)
    (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' := by
  rcases hsk with hsk | hsk
  · exact h.of_forward hf hsk hst hfloor
  · exact h.of_forward_cleared hf hsk hst hfloor

/-- A step that touches none of the fields the carrier reads. -/
lemma ColFloor.of_fields_eq {s s' : ScannerState} (h : ColFloor s)
    (hnic : s'.needIndentCheck = s.needIndentCheck) (hind : s'.indents = s.indents)
    (hcol : s'.col = s.col) (hline : s'.line = s.line)
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' :=
  h.of_forward (Forward.of_fields hline hcol) hsk hst (by
    rw [hnic, currentIndent_of_indents_eq hind, hcol]; exact h.floor)

/-- The floor on a same-line step that keeps the stack. -/
lemma floor_of_same_line {s s' : ScannerState} (hfl : s.currentIndent ≤ (s.col : Int))
    (hind : s'.indents = s.indents) (hline : s'.line = s.line) (hcol : s.col ≤ s'.col) :
    s'.currentIndent ≤ (s'.col : Int) := by
  rw [currentIndent_of_indents_eq hind]; have := hline; omega

lemma mk'_colfloor (input : String) : ColFloor (ScannerState.mk' input) where
  floor := by intro _; unfold ScannerState.mk' ScannerState.currentIndent; simp
  key := by intro h; unfold ScannerState.mk' at h; simp at h
  stack := by intro j hj; unfold ScannerState.mk' at hj; simp at hj

/-! ## §3  Preprocessing -/

lemma skipToContent_forward {s s' : ScannerState} (h : skipToContent s = .ok s') :
    Forward s s' := by
  have hl : s.line ≤ s'.line := by
    unfold skipToContent at h
    exact L4YAML.Proofs.StaleCursorFloor.skipToContentLoop_line_ge _ h
  rcases Nat.lt_or_eq_of_le hl with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq.symm,
      L4YAML.Proofs.StaleCursorFloor.skipToContent_col_ge_of_line_eq h heq.symm⟩

lemma skipToContent_colfloor {s s' : ScannerState} (h : ColFloor s) (hok : skipToContent s = .ok s') :
    ColFloor s' :=
  h.of_forward (skipToContent_forward hok)
    (L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_simpleKeyStack s s' hok)
    (by
      intro hnic
      have hnic0 : s.needIndentCheck = false := by
        cases h0 : s.needIndentCheck
        · rfl
        · exact absurd (skipToContent_needIndentCheck_mono hok h0)
            (by rw [hnic]; decide)
      have hline := skipToContent_line_eq_of_needIndentCheck s s' hok hnic
      exact floor_of_same_line (h.floor hnic0)
        (L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s' hok) hline
        (L4YAML.Proofs.StaleCursorFloor.skipToContent_col_ge_of_line_eq hok hline))

lemma saveSimpleKey_key_shape (st : ScannerState) :
    (saveSimpleKey st).simpleKey = st.simpleKey ∨
    ((saveSimpleKey st).simpleKey.possible = true ∧
      (saveSimpleKey st).simpleKey.pos = st.currentPos) := by
  unfold saveSimpleKey
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl

lemma saveSimpleKey_colfloor {s : ScannerState} (h : ColFloor s) : ColFloor (saveSimpleKey s) where
  floor := by
    rw [L4YAML.Proofs.PropsRunLineCoupling.saveSimpleKey_needIndentCheck,
      currentIndent_of_indents_eq (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents s),
      L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col]
    exact h.floor
  key := by
    intro hp
    have hf : Forward s (saveSimpleKey s) := Forward.of_fields
      (L4YAML.Proofs.PropsRunLineCoupling.saveSimpleKey_line s)
      (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col s)
    rcases saveSimpleKey_key_shape s with heq | ⟨_, hpos⟩
    · rw [heq] at hp ⊢; exact (h.key hp).mono hf
    · rw [hpos]; exact (Behind.of_pos s).mono hf
  stack := by
    intro j hj hp
    have hf : Forward s (saveSimpleKey s) := Forward.of_fields
      (L4YAML.Proofs.PropsRunLineCoupling.saveSimpleKey_line s)
      (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col s)
    simp only [L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack] at hj hp ⊢
    exact (h.stack j hj hp).mono hf

lemma closeStaleExplicitKey_colfloor {s : ScannerState} (h : ColFloor s) :
    ColFloor (closeStaleExplicitKey s) := by
  rcases L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_cases s with heq | ⟨_, _, heq⟩
  · rw [heq]; exact h
  · rw [heq]
    exact h.of_fields_eq rfl rfl rfl rfl rfl rfl

lemma unwindIndents_colfloor_at_col {s : ScannerState} (h : ColFloor s) (hbase : SentinelBase s) :
    ColFloor { unwindIndents s s.col with needIndentCheck := false } := by
  have hf : Forward s { unwindIndents s s.col with needIndentCheck := false } :=
    Forward.of_fields (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_line s _)
      (L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col s _)
  refine h.of_forward hf (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_simpleKey s _)
    (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_simpleKeyStack s _) ?_
  intro _
  show (unwindIndents s s.col).currentIndent ≤ ((unwindIndents s s.col).col : Int)
  rw [L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col]
  exact L4YAML.Proofs.IndentStackCover.unwindIndents_top_le hbase (Int.natCast_nonneg _)

/-- **Preprocessing keeps the floor.** -/
lemma preprocess_colfloor {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : ColFloor s)
    (hbase : SentinelBase s) : ColFloor s' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have hS : ColFloor s_skip := skipToContent_colfloor h h_skip
    have hB : SentinelBase s_skip := by
      unfold SentinelBase
      rw [L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s_skip h_skip]
      exact hbase
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact closeStaleExplicitKey_colfloor
              (saveSimpleKey_colfloor (unwindIndents_colfloor_at_col hS hB))
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact closeStaleExplicitKey_colfloor (saveSimpleKey_colfloor hS)

/-- **The bridge to item 338's STARVED premise.** -/
lemma preprocessFloor {s : ScannerState} (h : ColFloor s) (hbase : SentinelBase s) :
    PendingKeySound.PreprocessFloor s := by
  intro sp c hok hnf
  have hfl := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s sp c hok
  have hnf0 : s.inFlow = false := by
    first
      | simpa [ScannerState.inFlow, hfl] using hnf
      | simpa [ScannerState.inFlow, ← hfl] using hnf
  exact (preprocess_colfloor hok h hbase).floor
    (L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hnf0 hok)

/-- After preprocessing, the floor holds unconditionally once the structural
    dispatcher's flow check has passed (`underIndentedFlowContent`). -/
lemma dispatchStructural_floor {s : ScannerState} {c : Char} {r : Option ScannerState}
    (hok : scanNextToken_dispatchStructural s c = .ok r) (h : ColFloor s)
    (hnic : s.inFlow = false → s.needIndentCheck = false) :
    s.currentIndent ≤ (s.col : Int) := by
  by_cases hf : s.inFlow = true
  · unfold scanNextToken_dispatchStructural at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    split at hok
    · contradiction
    · rename_i hcond
      simp only [hf, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hcond
      omega
  · have hnf : s.inFlow = false := by simpa using hf
    exact h.floor (hnic hnf)

/-! ## §4  Structural arms -/

lemma unwindIndents_neg_one_currentIndent {s : ScannerState} (hbase : SentinelBase s) :
    (unwindIndents s (-1)).currentIndent ≤ -1 := by
  rcases L4YAML.Proofs.PreprocessIndentStable.unwindIndents_terminal s (-1) with h1 | h2
  · exact h1
  · rw [(L4YAML.Proofs.IndentStackBase.unwindIndents_base s (-1) hbase).currentIndent_of_size_le_one h2]
    exact Int.le_refl _

lemma scanDocumentStart_colfloor {s : ScannerState} (h : ColFloor s) (hbase : SentinelBase s) :
    ColFloor (scanDocumentStart s) := by
  have hind : (scanDocumentStart s).indents = (unwindIndents s (-1)).indents := by
    unfold scanDocumentStart
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents]
  have h1 : Forward s (unwindIndents s (-1)) := Forward.of_fields
    (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_line s (-1))
    (L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col s (-1))
  have hf : Forward s (scanDocumentStart s) := by
    unfold scanDocumentStart
    exact h1.trans ((Forward.of_fields (s' := { unwindIndents s (-1) with
      simpleKey := { possible := false } }) rfl rfl).trans ((Forward.emit _ _).trans
        ((Forward.advanceN _ 3).trans (Forward.of_fields rfl rfl))))
  refine h.of_forward_cleared hf ?_
    (L4YAML.Proofs.ScannerCorrectness.scanDocumentStart_preserves_simpleKeyStack s) ?_
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_simpleKey,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKey]
  · intro _
    rw [currentIndent_of_indents_eq hind]
    have := unwindIndents_neg_one_currentIndent hbase
    omega

set_option maxHeartbeats 800000 in
lemma scanDocumentEnd_shape {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s') :
    s' = { (({ unwindIndents s (-1) with simpleKey := { possible := false } }).emit
              .documentEnd).advanceN 3 with
            simpleKeyAllowed := true
            allowDirectives := true
            directivesPresent := false
            definedAnchors := #[]
            explicitKeyLine := none
            explicitKeyCol := -1 } := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals exact (Except.ok.inj hok).symm

lemma scanDocumentEnd_colfloor {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s')
    (h : ColFloor s) (hbase : SentinelBase s) : ColFloor s' := by
  have hst := L4YAML.Proofs.ScannerCorrectness.scanDocumentEnd_preserves_simpleKeyStack s s' hok
  have hshape := scanDocumentEnd_shape hok
  have h1 : Forward s (unwindIndents s (-1)) := Forward.of_fields
    (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_line s (-1))
    (L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col s (-1))
  have hf : Forward s s' := by
    rw [hshape]
    exact h1.trans ((Forward.of_fields (s' := { unwindIndents s (-1) with
      simpleKey := { possible := false } }) rfl rfl).trans ((Forward.emit _ _).trans
        ((Forward.advanceN _ 3).trans (Forward.of_fields rfl rfl))))
  have hind : s'.indents = (unwindIndents s (-1)).indents := by
    rw [hshape]
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents]
  refine h.of_forward_cleared hf ?_ hst ?_
  · rw [hshape]
    simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_simpleKey,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKey]
  · intro _
    rw [currentIndent_of_indents_eq hind]
    have := unwindIndents_neg_one_currentIndent hbase
    omega

lemma scanDirective_colfloor {s s' : ScannerState} (hpk : s.peek? = some '%') (hcol0 : s.col = 0)
    (hok : scanDirective s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨hl, hi⟩ := L4YAML.Proofs.StaleCursorFloor.scanDirective_line_ind hpk hok
  refine h.of_forward (Forward.of_same_line hl (by rw [hcol0]; exact Nat.zero_le _))
    (L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_simpleKeyStack s s' hok) ?_
  intro _
  rw [currentIndent_of_indents_eq hi]
  rw [hcol0] at hfl
  have : (0 : Int) ≤ (s'.col : Int) := Int.natCast_nonneg _
  omega

lemma dispatchStructural_colfloor {s s' : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : ColFloor s)
    (hbase : SentinelBase s) (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_colfloor h hbase
    | exact scanDocumentEnd_colfloor (by assumption) h hbase
    | (have hcond : (c == '%' && s.col == 0) = true := by assumption
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨hc, hc0⟩ := hcond
       subst hc
       exact scanDirective_colfloor hpk hc0 (by assumption) h hfl)

/-! ## §5  Flow arms -/

lemma emit_peek (s : ScannerState) (t : YamlToken) : (s.emit t).peek? = s.peek? := rfl

lemma emit_advance_cursor {s : ScannerState} {t : YamlToken} {c : Char} (hpk : s.peek? = some c)
    (hnb : isLineBreakBool c = false) :
    ((s.emit t).advance).line = s.line ∧ ((s.emit t).advance).col = s.col + 1 := by
  have := Forward.advance_of_nb (s := s.emit t) (c := c) (by rw [emit_peek]; exact hpk) hnb
  exact this

lemma scanFlowSequenceStart_colfloor {s : ScannerState} (hpk : s.peek? = some '[') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowSequenceStart s) := by
  have hf : Forward s (scanFlowSequenceStart s) := by
    unfold scanFlowSequenceStart
    exact (Forward.of_fields (s' := { s with simpleKey := { possible := false } }) rfl rfl).trans
      ((Forward.emit _ _).trans ((Forward.advance _).trans (Forward.of_fields rfl rfl)))
  have hline : (scanFlowSequenceStart s).line = s.line := by
    unfold scanFlowSequenceStart
    exact (Forward.advance_of_nb (s := ({ s with simpleKey := { possible := false } }).emit
      .flowSequenceStart) (c := '[') hpk (by decide)).1
  have hcol : s.col ≤ (scanFlowSequenceStart s).col := hf.col_le_of_line_eq hline
  have hst : (scanFlowSequenceStart s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
    unfold scanFlowSequenceStart
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowSequenceStart_preserves_indents s) hline hcol
  · intro hp
    rw [L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared] at hp; cases hp
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [Array.getElem_push] at hp ⊢
    split at hp
    · rename_i hlt
      simp only [hlt, ↓reduceDIte]
      exact (h.stack j hlt hp).mono hf
    · rename_i hge
      simp only [hge, ↓reduceDIte]
      exact (h.key hp).mono hf

lemma scanFlowMappingStart_colfloor {s : ScannerState} (hpk : s.peek? = some '{') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowMappingStart s) := by
  have hf : Forward s (scanFlowMappingStart s) := by
    unfold scanFlowMappingStart
    exact (Forward.of_fields (s' := { s with simpleKey := { possible := false } }) rfl rfl).trans
      ((Forward.emit _ _).trans ((Forward.advance _).trans (Forward.of_fields rfl rfl)))
  have hline : (scanFlowMappingStart s).line = s.line := by
    unfold scanFlowMappingStart
    exact (Forward.advance_of_nb (s := ({ s with simpleKey := { possible := false } }).emit
      .flowMappingStart) (c := '{') hpk (by decide)).1
  have hcol : s.col ≤ (scanFlowMappingStart s).col := hf.col_le_of_line_eq hline
  have hst : (scanFlowMappingStart s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
    unfold scanFlowMappingStart
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowMappingStart_preserves_indents s) hline hcol
  · intro hp
    rw [L4YAML.Proofs.ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared] at hp; cases hp
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [Array.getElem_push] at hp ⊢
    split at hp
    · rename_i hlt
      simp only [hlt, ↓reduceDIte]
      exact (h.stack j hlt hp).mono hf
    · rename_i hge
      simp only [hge, ↓reduceDIte]
      exact (h.key hp).mono hf

/-- A pop keeps the surviving entries behind the cursor; the restored key is
    the popped one. -/
lemma flowEnd_colfloor {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey = s.simpleKeyStack.back?.getD {})
    (hst : s'.simpleKeyStack = s.simpleKeyStack.pop)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' where
  floor := hfloor
  key := by
    intro hp
    rw [hsk, Array.back?_eq_getElem?] at hp ⊢
    cases hk : s.simpleKeyStack[s.simpleKeyStack.size - 1]? with
    | none => rw [hk] at hp; simp at hp
    | some k =>
      rw [hk] at hp
      simp only [Option.getD_some] at hp ⊢
      obtain ⟨hlt, hkk⟩ := Array.getElem?_eq_some_iff.mp hk
      rw [← hkk] at hp ⊢
      exact (h.stack _ hlt hp).mono hf
  stack := by
    intro j hj hp
    simp only [hst, Array.size_pop] at hj
    simp only [hst, Array.getElem_pop] at hp ⊢
    exact (h.stack j (by omega) hp).mono hf

lemma scanFlowSequenceEnd_colfloor {s : ScannerState} (hpk : s.peek? = some ']') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowSequenceEnd s) := by
  obtain ⟨hl, hc⟩ := L4YAML.Proofs.StaleCursorFloor.scanFlowSequenceEnd_cursor hpk
  refine flowEnd_colfloor h (Forward.of_same_line hl (by rw [hc]; exact Nat.le_succ _))
    (L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s) ?_ ?_
  · unfold scanFlowSequenceEnd
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowSequenceEnd_preserves_indents s) hl
      (by rw [hc]; exact Nat.le_succ _)

lemma scanFlowMappingEnd_colfloor {s : ScannerState} (hpk : s.peek? = some '}') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowMappingEnd s) := by
  obtain ⟨hl, hc⟩ := L4YAML.Proofs.StaleCursorFloor.scanFlowMappingEnd_cursor hpk
  refine flowEnd_colfloor h (Forward.of_same_line hl (by rw [hc]; exact Nat.le_succ _))
    (L4YAML.Proofs.ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s) ?_ ?_
  · unfold scanFlowMappingEnd
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowMappingEnd_preserves_indents s) hl
      (by rw [hc]; exact Nat.le_succ _)

lemma scanFlowEntry_colfloor {s s' : ScannerState} (hpk : s.peek? = some ',')
    (hok : scanFlowEntry s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack s s' hok
  have hind := L4YAML.Proofs.FlowIndentStable.scanFlowEntry_preserves_indents hok
  have hcl := L4YAML.Proofs.ScannerCorrectness.scanFlowEntry_clears_simpleKey s s' hok
  have hcur := emit_advance_cursor (s := s) (t := .flowEntry) (c := ',') hpk (by decide)
  have hlc : s'.line = s.line ∧ s'.col = s.col + 1 := by
    unfold scanFlowEntry at hok
    simp only [bind, Except.bind] at hok
    repeat (any_goals (split at hok))
    all_goals (try contradiction)
    all_goals (simp only [Except.ok.injEq] at hok; subst hok; exact hcur)
  exact h.of_forward_cleared (Forward.of_same_line hlc.1 (by rw [hlc.2]; exact Nat.le_succ _)) hcl hst
    (fun _ => floor_of_same_line hfl hind hlc.1 (by rw [hlc.2]; exact Nat.le_succ _))

lemma dispatchFlowIndicators_colfloor {s s' : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok))
  all_goals first
    | (have hc : (c == '[') = true := by assumption
       have hc' : c = '[' := by simpa using hc
       subst hc'; exact scanFlowSequenceStart_colfloor hpk h hfl)
    | (have hc : (c == '{') = true := by assumption
       have hc' : c = '{' := by simpa using hc
       subst hc'; exact scanFlowMappingStart_colfloor hpk h hfl)
    | (have hc : (c == ']') = true := by assumption
       have hc' : c = ']' := by simpa using hc
       subst hc'; exact scanFlowSequenceEnd_colfloor hpk h hfl)
    | (have hc : (c == '}') = true := by assumption
       have hc' : c = '}' := by simpa using hc
       subst hc'; exact scanFlowMappingEnd_colfloor hpk h hfl)
    | (have hc : (c == ',') = true := by assumption
       have hc' : c = ',' := by simpa using hc
       subst hc'; exact scanFlowEntry_colfloor hpk (by assumption) h hfl)
    | simp_all

/-! ## §6  Block arms -/

lemma pushMappingIndent_cursor (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).line = s.line ∧ (pushMappingIndent s col).col = s.col ∧
    (pushMappingIndent s col).peek? = s.peek? := by
  unfold pushMappingIndent ScannerState.emit ScannerState.peek?
  split <;> exact ⟨rfl, rfl, rfl⟩

lemma pushMappingIndent_currentIndent_ub (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).currentIndent = col ∨
    (pushMappingIndent s col).currentIndent = s.currentIndent := by
  unfold pushMappingIndent
  split
  · left
    simp [ScannerState.currentIndent, ScannerState.emit, Array.back?_push]
  · right; rfl

lemma scanBlockEntry_colfloor {s s' : ScannerState} (hnf : s.inFlow = false) (hpk : s.peek? = some '-')
    (hok : scanBlockEntry s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨hl, hc⟩ := L4YAML.Proofs.StaleCursorFloor.scanBlockEntry_line_col hnf hpk hok
  refine h.of_forward (Forward.of_same_line hl (by rw [hc]; exact Nat.le_succ _))
    (L4YAML.Proofs.ScannerCorrectness.scanBlockEntry_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanBlockEntry_preserves_simpleKeyStack s s' hok) ?_
  intro _
  rw [currentIndent_of_indents_eq
    (L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents hnf hok), hc]
  rcases L4YAML.Proofs.StaleCursorFloor.pushSequenceIndent_currentIndent_ub s (s.col : Int) with h1 | h1
  · rw [h1]; push_cast; omega
  · rw [h1]; push_cast; omega

lemma scanKey_shape {s s' : ScannerState} (hok : scanKey s = .ok s') :
    ∃ m : ScannerState, (m = pushMappingIndent s (s.col : Int) ∨ m = s) ∧
      s'.line = ((m.emit .key).advance).line ∧ s'.col = ((m.emit .key).advance).col ∧
      s'.simpleKey.possible = false ∧ s'.simpleKeyStack = m.simpleKeyStack := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals first
    | exact ⟨_, Or.inl rfl, rfl, rfl, rfl, by
        simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
          L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]⟩
    | exact ⟨_, Or.inr rfl, rfl, rfl, rfl, by
        simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
          L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]⟩

lemma scanKey_colfloor {s s' : ScannerState} (hpk : s.peek? = some '?')
    (hok : scanKey s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨m, hm, hl, hc, hsk, hst⟩ := scanKey_shape hok
  have hmc : m.line = s.line ∧ m.col = s.col ∧ m.peek? = s.peek? ∧
      m.simpleKeyStack = s.simpleKeyStack := by
    rcases hm with rfl | rfl
    · obtain ⟨a, b, c⟩ := pushMappingIndent_cursor s (s.col : Int)
      exact ⟨a, b, c, L4YAML.Proofs.ScannerCorrectness.pushMappingIndent_preserves_simpleKeyStack s _⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hml, hmcol, hmpk, hmst⟩ := hmc
  have hadv := Forward.advance_of_nb (s := m.emit .key) (c := '?') (by rw [emit_peek, hmpk]; exact hpk)
    (by decide)
  have hl' : s'.line = s.line :=
    ((hl.trans hadv.1).trans (show (m.emit .key).line = m.line from rfl)).trans hml
  have hc' : s'.col = s.col + 1 := by
    rw [hc, hadv.2]; exact congrArg (· + 1) ((show (m.emit .key).col = m.col from rfl).trans hmcol)
  refine h.of_forward_cleared (Forward.of_same_line hl' (by rw [hc']; exact Nat.le_succ _)) hsk
    (by rw [hst, hmst]) ?_
  intro _
  rw [hc']
  by_cases hf : s.inFlow = true
  · rw [currentIndent_of_indents_eq (L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow hf hok)]
    push_cast; omega
  · have hnf : s.inFlow = false := by simpa using hf
    rw [currentIndent_of_indents_eq (L4YAML.Proofs.PreprocessIndentStable.scanKey_indents hnf hok)]
    rcases pushMappingIndent_currentIndent_ub s (s.col : Int) with h1 | h1 <;> rw [h1] <;> push_cast <;> omega

lemma scanValueClearKey_fields (s : ScannerState) :
    (scanValueClearKey s).line = s.line ∧ (scanValueClearKey s).col = s.col ∧
    (scanValueClearKey s).peek? = s.peek? ∧
    (scanValueClearKey s).simpleKeyStack = s.simpleKeyStack ∧
    (scanValueClearKey s).inFlow = s.inFlow ∧
    ((scanValueClearKey s).simpleKey = s.simpleKey ∨ (scanValueClearKey s).simpleKey.possible = false) := by
  cases hek : s.explicitKeyLine with
  | none =>
    unfold scanValueClearKey; rw [hek]
    exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  | some ek =>
    unfold scanValueClearKey; rw [hek]
    dsimp only
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩

lemma scanValueValidate_key_line {s : ScannerState} {u : Unit} (hok : scanValueValidate s = .ok u)
    (hnf : s.inFlow = false) (hp : s.simpleKey.possible = true) : s.simpleKey.pos.line = s.line := by
  by_cases hl : s.simpleKey.pos.line = s.line
  · exact hl
  · exfalso
    unfold scanValueValidate at hok
    have hc : (s.simpleKey.possible && !s.inFlow && s.simpleKey.pos.line != s.line) = true := by
      simp [hp, hnf, hl]
    simp only [hc, ↓reduceIte] at hok
    simp [bind, Except.bind] at hok

lemma scanValuePrepare_fields (s : ScannerState) :
    (scanValuePrepare s).line = s.line ∧ (scanValuePrepare s).col = s.col ∧
    (scanValuePrepare s).peek? = s.peek? ∧
    (scanValuePrepare s).simpleKeyStack = s.simpleKeyStack ∧
    ((scanValuePrepare s).simpleKey.possible = false ∨ (scanValuePrepare s).simpleKey = s.simpleKey) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
    · split
      · obtain ⟨a, b, c⟩ := pushMappingIndent_cursor s (s.col : Int)
        exact ⟨a, b, c, L4YAML.Proofs.ScannerCorrectness.pushMappingIndent_preserves_simpleKeyStack s _,
          Or.inr (L4YAML.Proofs.ScannerCorrectness.pushMappingIndent_preserves_simpleKey s _)⟩
      · exact ⟨rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- The `:` opener's floor: with a live key the block mapping opens at the
    KEY's column, which the carrier's key lane puts at or left of the cursor. -/
lemma scanValuePrepare_floor {s : ScannerState}
    (hk : s.inFlow = false → s.simpleKey.possible = true → (s.simpleKey.pos.col : Int) ≤ s.col)
    (hfl : s.currentIndent ≤ (s.col : Int)) :
    (scanValuePrepare s).currentIndent ≤ (s.col : Int) := by
  unfold scanValuePrepare
  split
  · rename_i h_poss
    split
    · rename_i hnf
      split
      · show ((_ : ScannerState)).currentIndent ≤ _
        simp only [ScannerState.currentIndent]
        rw [Array.back?_push]
        simp only []
        exact hk (by simpa using hnf) h_poss
      · exact hfl
    · exact hfl
  · split
    · exact hfl
    · split
      · exact L4YAML.Proofs.IndentStackCover.pushMappingIndent_top_le hfl
      · exact hfl

lemma scanValue_colfloor {s s' : ScannerState} (hpk : s.peek? = some ':')
    (hok : scanValue s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨hkl, hkc, hkpk, hkst, hkf, hksk⟩ := scanValueClearKey_fields s
  obtain ⟨hpl, hpc, hppk, hpst, hpsk⟩ := scanValuePrepare_fields (scanValueClearKey s)
  have hkind := (PendingKeySound.scanValueClearKey_core s).1
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  have hval : ∃ u, scanValueValidate (scanValueClearKey s) = .ok u := by
    cases hx : scanValueValidate (scanValueClearKey s) with
    | error e => rw [hx] at hok; simp at hok
    | ok u => exact ⟨u, rfl⟩
  obtain ⟨u, hval⟩ := hval
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  have hok' := Except.ok.inj hok
  have hsl : s'.line = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.line := by
    rw [← hok']
  have hsc : s'.col = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.col := by
    rw [← hok']
  have hsi : s'.indents = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.indents := by
    rw [← hok']
  have hssk : s'.simpleKey = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.simpleKey := by
    rw [← hok']
  have hsst : s'.simpleKeyStack =
      ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.simpleKeyStack := by
    rw [← hok']
  have hadv := Forward.advance_of_nb (s := (scanValuePrepare (scanValueClearKey s)).emit .value)
    (c := ':') (by rw [emit_peek, hppk, hkpk]; exact hpk) (by decide)
  have hl' : s'.line = s.line := ((hsl.trans hadv.1).trans hpl).trans hkl
  have hc' : s'.col = s.col + 1 := by
    rw [hsc, hadv.2]; exact congrArg (· + 1) (hpc.trans hkc)
  have hf : Forward s s' := Forward.of_same_line hl' (by rw [hc']; exact Nat.le_succ _)
  have hkey_kc : (scanValueClearKey s).inFlow = false →
      (scanValueClearKey s).simpleKey.possible = true →
      ((scanValueClearKey s).simpleKey.pos.col : Int) ≤ (scanValueClearKey s).col := by
    intro hnf hp
    have hline := scanValueValidate_key_line hval hnf hp
    rcases hksk with heq | hcl
    · rw [heq] at hp hline ⊢
      rw [hkl] at hline
      have hb := h.key hp
      unfold Behind at hb
      rw [hkc]
      omega
    · rw [hcl] at hp; cases hp
  have hfl_kc : (scanValueClearKey s).currentIndent ≤ ((scanValueClearKey s).col : Int) := by
    rw [currentIndent_of_indents_eq hkind, hkc]; exact hfl
  have hpfl := scanValuePrepare_floor hkey_kc hfl_kc
  refine h.of_forward_or hf ?_ ?_ ?_
  · rw [hssk, L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKey,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKey]
    rcases hpsk with hcl | heq
    · exact Or.inr hcl
    · rw [heq]; exact hksk
  · rw [hsst, L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack, hpst, hkst]
  · intro _
    rw [hc']
    have hind' : s'.indents = (scanValuePrepare (scanValueClearKey s)).indents := by
      rw [hsi, L4YAML.Proofs.ScannerLoopInvariant.advance_indents, L4YAML.Proofs.ScannerContracts.emit_indents]
    rw [currentIndent_of_indents_eq hind']
    rw [hkc] at hpfl
    push_cast; omega

lemma dispatchBlockIndicators_colfloor {s s' : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals (first
    | (rename_i hcond _ _ hbe
       simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
       obtain ⟨⟨hc, hnf⟩, _⟩ := hcond
       subst hc
       exact scanBlockEntry_colfloor hnf hpk hbe h hfl)
    | (rename_i _ hcond _ _ hk
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨⟨⟨hc, _⟩, _⟩, _⟩ := hcond
       subst hc
       exact scanKey_colfloor hpk hk h hfl)
    | (rename_i _ _ hcond _ _ hv
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨hc, _⟩ := hcond
       subst hc
       exact scanValue_colfloor hpk hv h hfl))

/-! ## §7  Content arms -/

/-- A same-line step that moves the cursor right and keeps keys, stack and
    indents keeps the whole carrier (the floor is unconditional). -/
lemma ColFloor.of_cursor {s s' : ScannerState} (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int))
    (hl : s'.line = s.line) (hc : s.col ≤ s'.col) (hind : s'.indents = s.indents)
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' :=
  h.of_forward (Forward.of_same_line hl hc) hsk hst (fun _ => floor_of_same_line hfl hind hl hc)

/-- A scalar step: the cursor moves forward; on its entry line the column
    only grew, off it the cursor is strictly past the floor. -/
lemma ColFloor.of_scalar {s s' : ScannerState} (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int))
    (hline : s.line ≤ s'.line) (hsame : s'.line = s.line → s.col ≤ s'.col)
    (hcross : s'.line ≠ s.line → s.currentIndent < (s'.col : Int))
    (hind : s'.indents = s.indents)
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' := by
  have hf : Forward s s' := by
    rcases Nat.lt_or_eq_of_le hline with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq.symm, hsame heq.symm⟩
  refine h.of_forward hf hsk hst ?_
  intro _
  rw [currentIndent_of_indents_eq hind]
  by_cases heq : s'.line = s.line
  · have := hsame heq; omega
  · exact Int.le_of_lt (hcross heq)

lemma scanDoubleQuoted_colfloor {s s' : ScannerState} (hpk : s.peek? = some '"')
    (hok : scanDoubleQuoted s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hline : s.line ≤ s'.line := by
    unfold scanDoubleQuoted at hok
    simp only [bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i res h_loop
      have h_fields : s'.line = res.2.line := by
        repeat (any_goals (split at hok))
        all_goals (try contradiction)
        all_goals (first
          | (rw [← Except.ok.inj hok]; done)
          | (rw [← Except.ok.inj hok]; simp only [ScannerState.emitAt]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; simp only [ScannerState.emitAt]))
      rw [h_fields]
      have h1 := L4YAML.Proofs.ScalarProduction.collectDoubleQuotedLoop_line_ge s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd 0 h_loop
      have h2 := (Forward.advance_of_nb hpk (by decide)).1
      omega
  exact h.of_scalar hfl hline
    (fun hl => L4YAML.Proofs.ScalarWalkColFloor.scanDoubleQuoted_sameline_col_ge hpk hok hl)
    (fun hne => L4YAML.Proofs.ScalarWalkColFloor.scanDoubleQuoted_crossline_col_floor hpk hok hne)
    (L4YAML.Proofs.EmitterScannability.scanDoubleQuoted_preserves_indents s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s s' hok)

lemma scanSingleQuoted_colfloor {s s' : ScannerState} (hpk : s.peek? = some '\'')
    (hok : scanSingleQuoted s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hline : s.line ≤ s'.line := by
    unfold scanSingleQuoted at hok
    simp only [bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i res h_loop
      have h_fields : s'.line = res.2.line := by
        repeat (any_goals (split at hok))
        all_goals (try contradiction)
        all_goals (first
          | (rw [← Except.ok.inj hok]; done)
          | (rw [← Except.ok.inj hok]; simp only [ScannerState.emitAt]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; simp only [ScannerState.emitAt]))
      rw [h_fields]
      have h1 := L4YAML.Proofs.ScalarProduction.collectSingleQuotedLoop_line_ge s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd h_loop
      have h2 := (Forward.advance_of_nb hpk (by decide)).1
      omega
  exact h.of_scalar hfl hline
    (fun hl => L4YAML.Proofs.ScalarWalkColFloor.scanSingleQuoted_sameline_col_ge hpk hok hl)
    (fun hne => L4YAML.Proofs.ScalarWalkColFloor.scanSingleQuoted_crossline_col_floor hpk hok hne)
    (L4YAML.Proofs.FlowIndentStable.scanSingleQuoted_preserves_indents hok)
    (L4YAML.Proofs.ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s s' hok)

/-- **The flow plain-scalar loop keeps the cursor on its entry line (column
    grown) or strictly past the enclosing block floor** — the `[69]
    s-flow-line-prefix(n)` check on every folded continuation
    (`underIndentedScalar`), item 50 §8.1. -/
lemma collectPlainScalarLoop_flow_inv (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie l₀ c₀ : Nat) (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel true ci ie = .ok r →
    ((s.line = l₀ ∧ c₀ ≤ s.col) ∨ (l₀ < s.line ∧ s.currentIndent < (s.col : Int))) →
    (r.state.line = l₀ ∧ c₀ ≤ r.state.col) ∨
      (l₀ < r.state.line ∧ r.state.currentIndent < (r.state.col : Int)) := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie l₀ c₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    cases hok; exact hinv
  | succ fuel ih =>
    intro s content spaces ci ie l₀ c₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq; exact hinv
    · rename_i c hpk
      split at hok
      · rename_i res hterm
        injection hok with h_eq; subst h_eq
        exact (L4YAML.Proofs.ScalarWalkColFloor.terminates?_state hterm) ▸ hinv
      · have hadv : ∀ s'' : ScannerState, s''.line = s.line → s.col ≤ s''.col → s''.indents = s.indents →
            (s''.line = l₀ ∧ c₀ ≤ s''.col) ∨ (l₀ < s''.line ∧ s''.currentIndent < (s''.col : Int)) := by
          intro s'' hl hc hi
          rw [hl, currentIndent_of_indents_eq hi]
          rcases hinv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, Nat.le_trans h2 hc⟩
          · exact Or.inr ⟨h1, by omega⟩
        split at hok
        · -- line break, flow context: fold, floor check, recurse
          split at hok
          · generalize hfold : foldQuotedNewlines s = fr at hok
            cases fr with
            | error e => simp [bind, Except.bind] at hok
            | ok p =>
              obtain ⟨folded, s_f⟩ := p
              simp only [bind, Except.bind] at hok
              split at hok
              · injection hok with h_eq; subst h_eq; exact hinv
              · split at hok
                · simp [throw, throwThe, MonadExceptOf.throw] at hok
                · rename_i hcheck
                  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hcheck
                  have hlt := L4YAML.Proofs.ScalarProduction.foldQuotedNewlines_line_lt hpk (by assumption) hfold
                  have hinv_f : (s_f.line = l₀ ∧ c₀ ≤ s_f.col) ∨
                      (l₀ < s_f.line ∧ s_f.currentIndent < (s_f.col : Int)) := by
                    right
                    refine ⟨?_, ?_⟩
                    · rcases hinv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
                    · by_cases h0 : s_f.currentIndent ≥ 0
                      · have := hcheck h0; omega
                      · have : (0 : Int) ≤ (s_f.col : Int) := Int.natCast_nonneg _
                        omega
                  generalize h_loop :
                    collectPlainScalarLoop s_f (content ++ folded) "" fuel true ci ie = cont at hok
                  cases cont with
                  | ok inner =>
                    dsimp only at hok
                    split at hok
                    · injection hok with h_eq; subst h_eq; exact hinv
                    · have h_eq := Except.ok.inj hok; subst h_eq
                      exact ih _ _ _ _ _ _ _ _ h_loop hinv_f
                  | error e => simp at hok
          · rename_i hflow; exact absurd rfl hflow
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          split at hok
          · exact ih _ _ _ _ _ _ _ _ hok (hadv s.advance (Forward.advance_of_nb hpk hnb).1
              (by rw [(Forward.advance_of_nb hpk hnb).2]; exact Nat.le_succ _)
              (L4YAML.Proofs.ScannerLoopInvariant.advance_indents s))
          · split at hok
            · injection hok with h_eq; subst h_eq; exact hinv
            · exact ih _ _ _ _ _ _ _ _ hok (hadv s.advance (Forward.advance_of_nb hpk hnb).1
                (by rw [(Forward.advance_of_nb hpk hnb).2]; exact Nat.le_succ _)
                (L4YAML.Proofs.ScannerLoopInvariant.advance_indents s))

lemma scanPlainScalar_colfloor {s s' : ScannerState} (hok : scanPlainScalar s = .ok s')
    (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  have hind := L4YAML.Proofs.FlowIndentStable.scanPlainScalar_preserves_indents hok
  have hsk := L4YAML.Proofs.ScannerCorrectness.scanPlainScalar_preserves_simpleKey s s' hok
  have hst := L4YAML.Proofs.ScannerCorrectness.scanPlainScalar_preserves_simpleKeyStack s s' hok
  by_cases hf : s.inFlow = true
  · unfold scanPlainScalar at hok
    simp only [bind, Except.bind, hf, ↓reduceIte] at hok
    split at hok
    · cases hok
    · rename_i r h_loop
      have h_eq := Except.ok.inj hok
      have h_line : s'.line = r.state.line := by rw [← h_eq]; rfl
      have h_col : s'.col = r.state.col := by rw [← h_eq]; rfl
      have h_ind : r.state.indents = s.indents := by
        rw [← hind, ← h_eq]; rfl
      rcases collectPlainScalarLoop_flow_inv _ s "" "" s.col s.inputEnd s.line s.col r h_loop
        (Or.inl ⟨rfl, Nat.le_refl _⟩) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h.of_cursor hfl (by rw [h_line, h1]) (by rw [h_col]; exact h2) hind hsk hst
      · rw [currentIndent_of_indents_eq h_ind] at h2
        refine h.of_forward (Or.inl (by rw [h_line]; exact h1)) hsk hst ?_
        intro _
        rw [currentIndent_of_indents_eq hind, h_col]; exact Int.le_of_lt h2
  · have hnf : s.inFlow = false := by simpa using hf
    have hline : s.line ≤ s'.line := by
      unfold scanPlainScalar at hok
      simp only [bind, Except.bind, hnf, Bool.false_eq_true, ↓reduceIte] at hok
      split at hok
      · cases hok
      · rename_i r h_loop
        have h_eq := Except.ok.inj hok
        have h_line : s'.line = r.state.line := by rw [← h_eq]; rfl
        rw [h_line]
        exact L4YAML.Proofs.ScalarProduction.collectPlainScalarLoop_line_le s "" "" _ false _ s.inputEnd h_loop
    exact h.of_scalar hfl hline
      (fun hl => L4YAML.Proofs.ScalarWalkColFloor.scanPlainScalar_sameline_col_ge hnf hok hl)
      (fun hne => L4YAML.Proofs.ScalarWalkColFloor.scanPlainScalar_crossline_col_floor hnf hok hne)
      hind hsk hst

/-! ### Block scalars

The body walk never moves the cursor backwards (`Forward`), and it either
consumed the header's line break — after which `needIndentCheck` stays set
through the whole body (`collectBlockScalarLoop_nic_mono`) — or the header
ran into end-of-input on its own line, where the column only grew. -/

section BlockScalar
open L4YAML.Scanner L4YAML.Proofs.LineOpenGuard L4YAML.Proofs.IndentStackBase

lemma consumeNewline_forward (s : ScannerState) : Forward s (consumeNewline s) := by
  unfold consumeNewline
  split
  · exact Forward.advance s
  · refine (Forward.advance s).trans ?_
    (try dsimp only)
    split <;> exact Forward.of_fields rfl rfl
  · exact Forward.refl s

lemma consumeExactSpaces_forward (count : Nat) :
    ∀ s : ScannerState, Forward s (consumeExactSpaces s count).2 := by
  induction count with
  | zero => intro s; exact Forward.refl s
  | succ n ih =>
    intro s
    unfold consumeExactSpaces
    split
    · exact (Forward.advance s).trans (ih s.advance)
    · exact Forward.refl s

lemma collectLineContentLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (content : String), Forward s (collectLineContentLoop s content fuel).2 := by
  induction fuel with
  | zero => intro s content; exact Forward.refl s
  | succ n ih =>
    intro s content
    unfold collectLineContentLoop
    split
    · split
      · exact Forward.refl s
      · exact (Forward.advance s).trans (ih _ _)
    · exact Forward.refl s

lemma collectBlockScalarLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (raw : String) (ci ie : Nat),
    Forward s (collectBlockScalarLoop s raw fuel ci ie).2 := by
  induction fuel with
  | zero => intro s raw ci ie; exact Forward.refl s
  | succ n ih =>
    intro s raw ci ie
    unfold collectBlockScalarLoop
    split
    · exact Forward.refl s
    · split
      rename_i sp sa heq
      have h1 : Forward s sa := by
        have := consumeExactSpaces_forward ci s
        rw [heq] at this; exact this
      split
      · exact h1
      · split
        · exact h1.trans ((consumeNewline_forward _).trans (ih _ _ _ _))
        · split
          · exact Forward.refl s
          · (try dsimp only)
            have h2 := collectLineContentLoop_forward (ie - sa.offset + 1) sa ""
            split
            · split
              · exact h1.trans (h2.trans ((consumeNewline_forward _).trans (ih _ _ _ _)))
              · split
                · exact Forward.refl s
                · exact h1.trans h2
            · (try dsimp only)
              (try split) <;> exact h1.trans h2

lemma parseBlockHeaderLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (ch : ChompStyle) (m : Option Nat),
    Forward s (parseBlockHeaderLoop s ch m fuel).2.2 := by
  induction fuel with
  | zero => intro s ch m; exact Forward.refl s
  | succ n ih =>
    intro s ch m
    unfold parseBlockHeaderLoop
    split
    · exact (Forward.advance s).trans (ih _ _ _)
    · exact (Forward.advance s).trans (ih _ _ _)
    · split
      · exact (Forward.advance s).trans (ih _ _ _)
      · exact Forward.refl s
    · exact Forward.refl s

lemma parseBlockHeaderLoop_line (fuel : Nat) :
    ∀ (s : ScannerState) (ch : ChompStyle) (m : Option Nat),
    (parseBlockHeaderLoop s ch m fuel).2.2.line = s.line := by
  induction fuel with
  | zero => intro s ch m; unfold parseBlockHeaderLoop; rfl
  | succ n ih =>
    intro s ch m
    unfold parseBlockHeaderLoop
    have hpeek : ∀ c, peekBlockHeaderIndicator? s ch m = some c → s.peek? = some c := by
      intro c h; unfold peekBlockHeaderIndicator? at h
      split at h <;> (try split at h) <;> simp_all
    split
    · rename_i hpk
      rw [ih, advance_preserves_line_of_ne_break s '-' (hpeek _ hpk) (by decide) (by decide)]
    · rename_i hpk
      rw [ih, advance_preserves_line_of_ne_break s '+' (hpeek _ hpk) (by decide) (by decide)]
    · rename_i c _ _ hpk
      split
      · rename_i hd
        rw [ih, advance_preserves_line_of_ne_break s c (hpeek _ hpk)]
        · intro hc; subst hc; simp at hd
        · intro hc; subst hc; simp at hd
      · rfl
    · rfl

lemma collectCommentTextLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (text : String), Forward s (collectCommentTextLoop s text fuel).2 := by
  induction fuel with
  | zero => intro s text; unfold collectCommentTextLoop; exact Forward.refl s
  | succ n ih =>
    intro s text
    unfold collectCommentTextLoop
    split
    · split
      · exact Forward.refl s
      · exact (Forward.advance s).trans (ih _ _)
    · exact Forward.refl s

lemma scanBlockScalarSkipComment_forward (s : ScannerState) :
    Forward s (scanBlockScalarSkipComment s) := by
  unfold scanBlockScalarSkipComment
  repeat (any_goals (first | (dsimp only; split) | split))
  all_goals (first
    | exact Forward.refl s
    | exact (Forward.advance s).trans
        ((collectCommentTextLoop_forward (s.advance.inputEnd - s.advance.offset) s.advance "").trans
          (Forward.of_fields rfl rfl)))

lemma scanBlockScalarSkipComment_line (s : ScannerState) :
    (scanBlockScalarSkipComment s).line = s.line := by
  unfold scanBlockScalarSkipComment
  split
  · rename_i hpk
    repeat (any_goals (first | (dsimp only; split) | split))
    all_goals (first
      | rfl
      | exact (collectCommentTextLoop_preserves_line s.advance "" (s.advance.inputEnd - s.advance.offset)).trans
          (advance_preserves_line_of_ne_break s '#' hpk (by decide) (by decide)))
  · rfl

lemma skipWhitespace_forward (s : ScannerState) : Forward s (skipWhitespace s) :=
  Forward.of_same_line (skipWhitespace_preserves_line s)
    (L4YAML.Proofs.ScalarWalkColFloor.skipWhitespace_col_ge s)

lemma scanBlockScalarBody_forward {s_orig s_nl s' : ScannerState} {chomp : ChompStyle}
    {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    Forward s_nl s' := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; (try dsimp only))
  all_goals (exact (collectBlockScalarLoop_forward _ s_nl "" _ _).trans (Forward.of_fields rfl rfl))

lemma scanBlockScalarBody_atEnd_line {s_orig s_nl s' : ScannerState} {chomp : ChompStyle}
    {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (hs : s_nl.peek? = none)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.line = s_nl.line := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; (try dsimp only))
  all_goals (rw [collectBlockScalarLoop_atEnd hs]; unfold ScannerState.emitAt; rfl)

lemma scanBlockScalar_colfloor {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanBlockScalar s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hind := scanBlockScalar_preserves_indents hok
  have hsk := L4YAML.Proofs.ScannerCorrectness.scanBlockScalar_clears_simpleKey s s' hok
  have hst := L4YAML.Proofs.ScannerCorrectness.scanBlockScalar_preserves_simpleKeyStack s s' hok
  have hf_hdr : Forward s (scanBlockScalarSkipComment
      (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)) :=
    (Forward.advance s).trans ((parseBlockHeaderLoop_forward 2 _ _ _).trans
      ((skipWhitespace_forward _).trans (scanBlockScalarSkipComment_forward _)))
  have hl_hdr : (scanBlockScalarSkipComment
      (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)).line = s.line := by
    rw [scanBlockScalarSkipComment_line, skipWhitespace_preserves_line, parseBlockHeaderLoop_line,
      (Forward.advance_of_nb hpk hnb).1]
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  split at hok
  · cases hok
  · rename_i s_nl hnl
    have hf_body : Forward s_nl s' := scanBlockScalarBody_forward hok
    have key : Forward (scanBlockScalarSkipComment
        (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)) s_nl ∧
        (s'.needIndentCheck = true ∨
          (s_nl.peek? = none ∧ (scanBlockScalarSkipComment
            (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)) = s_nl)) := by
      unfold scanBlockScalarConsumeNewline at hnl
      split at hnl
      · rename_i c₀ hpk₀
        split at hnl
        · rename_i hbr₀
          have := Except.ok.inj hnl; subst this
          exact ⟨consumeNewline_forward _, Or.inl (scanBlockScalarBody_nic_mono
            (consumeNewline_needIndentCheck_of_break _ c₀ hpk₀ hbr₀) hok)⟩
        · split at hnl
          · rename_i hnomore
            have hs_eq := Except.ok.inj hnl
            refine ⟨hs_eq ▸ Forward.refl _, Or.inr ⟨?_, hs_eq⟩⟩
            rw [← hs_eq]
            unfold ScannerState.peek?; rw [ite_eq_right]
            simp only [Bool.not_eq_true', ScannerState.hasMore,
              decide_eq_false_iff_not] at hnomore
            exact hnomore
          · cases hnl
      · rename_i hpk₀
        have hs_eq := Except.ok.inj hnl
        exact ⟨hs_eq ▸ Forward.refl _, Or.inr ⟨by rw [← hs_eq]; exact hpk₀, hs_eq⟩⟩
    refine h.of_forward_cleared (hf_hdr.trans (key.1.trans hf_body)) hsk hst ?_
    intro hnic
    rcases key.2 with hn | ⟨hpkn, hs_eq⟩
    · rw [hn] at hnic; cases hnic
    · rw [currentIndent_of_indents_eq hind, scanBlockScalarBody_atEnd hpkn hok, ← hs_eq]
      have := hf_hdr.col_le_of_line_eq hl_hdr
      omega

end BlockScalar

/-! ### The content dispatcher -/

open L4YAML.Proofs.StaleCursorFloor L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.BlockScalarFlowGuard L4YAML.Scanner in
lemma dispatchContent_colfloor {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- '&': anchor, then the definedAnchors touch-up
    split at hok
    · simp at hok
    split at hok
    · simp at hok
    · rename_i s_a h_anch
      simp only [Except.ok.injEq] at hok; subst hok
      obtain ⟨hl, hc, hi⟩ := scanAnchorOrAlias_cursor hpk hnb h_anch
      exact (h.of_cursor hfl hl hc hi (scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch)
        (scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_anch)).of_fields_eq
        rfl rfl rfl rfl rfl rfl
  · split at hok
    · -- '*': alias
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · replace hok := aliasArm_scan_ok hok
        obtain ⟨hl, hc, hi⟩ := scanAnchorOrAlias_cursor hpk hnb hok
        exact h.of_cursor hfl hl hc hi (scanAnchorOrAlias_preserves_simpleKey s false s' hok)
          (scanAnchorOrAlias_preserves_simpleKeyStack s false s' hok)
    · split at hok
      · -- '!': tag
        rename_i h_c
        split at hok
        · simp at hok
        · have h_cq : c = '!' := by simpa using h_c
          subst h_cq
          obtain ⟨hl, hc, hi⟩ := scanTag_cursor hpk hok
          exact h.of_cursor hfl hl hc hi (scanTag_preserves_simpleKey s s' hok)
            (scanTag_preserves_simpleKeyStack s s' hok)
      · split at hok
        · -- '|' / '>'
          exact scanBlockScalar_colfloor hpk hnb (peel_blockScalarGuard hok) h hfl
        · split at hok
          · -- '"'
            rename_i h_c
            split at hok
            · simp at hok
            · rename_i s_dq h_dq
              have h_cq : c = '"' := by simpa using h_c
              subst h_cq
              have hcf := scanDoubleQuoted_colfloor hpk h_dq h hfl
              split at hok <;> (simp only [Except.ok.injEq] at hok; subst hok)
              · exact hcf.of_touchup rfl rfl rfl rfl rfl rfl rfl
              · exact hcf
          · split at hok
            · -- '\''
              rename_i h_c
              split at hok
              · simp at hok
              · rename_i s_sq h_sq
                have h_cq : c = '\'' := by simpa using h_c
                subst h_cq
                have hcf := scanSingleQuoted_colfloor hpk h_sq h hfl
                split at hok <;> (simp only [Except.ok.injEq] at hok; subst hok)
                · exact hcf.of_touchup rfl rfl rfl rfl rfl rfl rfl
                · exact hcf
            · split at hok
              · exact scanPlainScalar_colfloor hok h hfl
              · simp at hok

/-! ## §8  The token step and the seed -/

/-- The character preprocessing hands the dispatchers is never a line break
    (`skipToContent` consumes every break before stopping). -/
lemma preprocess_not_break {s sp : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (sp, c))) : isLineBreakBool c = false := by
  have hpeek := L4YAML.Proofs.ScannerCorrectness.preprocess_peek_eq s sp c hok
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · simp at hok
    · have h_sc_peek : s_content.peek? = some c := by
        split at hok
        all_goals (
          split at hok
          <;> (try simp at hok)
          <;> (split at hok
            <;> (try simp at hok)
            <;> (obtain ⟨h1, _⟩ := hok; subst h1
                 first
                 | (rw [L4YAML.Proofs.PendingKeySound.closeStaleExplicitKey_peek, L4YAML.Proofs.ScanStrictCoupling.saveSimpleKey_peek] at hpeek
                    unfold ScannerState.peek? unwindIndents at hpeek
                    simp only [L4YAML.Proofs.ScanStrictCoupling.unwindIndentsLoop_offset, L4YAML.Proofs.ScanStrictCoupling.unwindIndentsLoop_inputEnd,
                      L4YAML.Proofs.ScanStrictCoupling.unwindIndentsLoop_input] at hpeek
                    exact hpeek)
                 | (rw [L4YAML.Proofs.PendingKeySound.closeStaleExplicitKey_peek, L4YAML.Proofs.ScanStrictCoupling.saveSimpleKey_peek] at hpeek
                    exact hpeek))))
      exact L4YAML.Proofs.PreprocessProduction.skipToContent_peek_not_break s s_content c h_skip h_sc_peek

/-- **`ColFloor` through one token** — the carrier the flip's premise is read
    off at every `scanLoop` boundary. -/
lemma scanNextToken_colfloor {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : ColFloor s) (hbase : SentinelBase s) : ColFloor s' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp c h_pre
      have hcf : ColFloor sp := preprocess_colfloor h_pre h hbase
      have hpk : sp.peek? = some c := L4YAML.Proofs.ScannerCorrectness.preprocess_peek_eq s sp c h_pre
      have hnb : isLineBreakBool c = false := preprocess_not_break h_pre
      have hpb : SentinelBase sp := L4YAML.Proofs.IndentStackBase.preprocess_base h_pre hbase
      have hnic : sp.inFlow = false → sp.needIndentCheck = false := by
        intro hnf
        have hfl := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s sp c h_pre
        have hnf0 : s.inFlow = false := by
          first
            | simpa [ScannerState.inFlow, hfl] using hnf
            | simpa [ScannerState.inFlow, ← hfl] using hnf
        exact L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hnf0 h_pre
      split at hok
      · cases hok
      split at hok
      · cases hok
      split at hok
      · cases hok
      · split at hok
        · rename_i s_ds h_ds
          simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact dispatchStructural_colfloor hpk h_ds hcf hpb (dispatchStructural_floor h_ds hcf hnic)
        · rename_i h_ds
          have hfl : sp.currentIndent ≤ (sp.col : Int) := dispatchStructural_floor h_ds hcf hnic
          split at hok
          · cases hok
          split at hok
          · cases hok
          · rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at hok
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_colfloor hpk h_fi hcf hfl
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_colfloor hpk h_bi hcf hfl
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_colfloor hpk hnb h_dc hcf hfl
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have hcf2 : ColFloor sp2 := by
                rw [← h_sp2]; exact hcf.of_fields_eq rfl rfl rfl rfl rfl rfl
              have hpk2 : sp2.peek? = some c := by rw [← h_sp2]; exact hpk
              have hfl2 : sp2.currentIndent ≤ (sp2.col : Int) := by rw [← h_sp2]; exact hfl
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_colfloor hpk2 h_fi hcf2 hfl2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_colfloor hpk2 h_bi hcf2 hfl2
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp2 c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp2 c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_colfloor hpk2 hnb h_dc hcf2 hfl2

/-- **The consumer item 338 left STARVED**: `scanNextToken_sound` with its
    `PreprocessFloor` premise paid by the carrier.  Both invariants ride one
    token step together. -/
lemma scanNextToken_sound_colfloor {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s'))
    (h : L4YAML.Proofs.PendingKeySound.Sound s) (hm : L4YAML.Proofs.IndentStackMono.Mono s) (hbase : SentinelBase s) (hcf : ColFloor s) :
    L4YAML.Proofs.PendingKeySound.Sound s' ∧ ColFloor s' :=
  ⟨L4YAML.Proofs.PendingKeySound.scanNextToken_sound hok h hm hbase (preprocessFloor hcf hbase),
   scanNextToken_colfloor hok hcf hbase⟩

/-! ### The `scan` seed: `mk'`, the `streamStart` emission, and §5.2's BOM -/

lemma seed_colfloor (input : String) :
    ColFloor ((ScannerState.mk' input).emit .streamStart) :=
  (mk'_colfloor input).of_fields_eq rfl rfl rfl rfl rfl rfl

lemma seed_bom_colfloor (input : String)
    (hpk : ((ScannerState.mk' input).emit .streamStart).peek? = some '\uFEFF') :
    ColFloor ((ScannerState.mk' input).emit .streamStart).consumeBOM := by
  refine (seed_colfloor input).of_forward_cleared ?_ ?_ ?_ ?_
  · exact Forward.of_same_line (Forward.advance_of_nb hpk (by decide)).1
      (by simp [ScannerState.emit, ScannerState.mk'])
  · show (((ScannerState.mk' input).emit .streamStart).advance).simpleKey.possible = false
    rw [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKey]
    simp [ScannerState.emit, ScannerState.mk']
  · exact L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack _
  · intro _
    show (((ScannerState.mk' input).emit .streamStart).advance).currentIndent ≤ ((0 : Nat) : Int)
    rw [currentIndent_of_indents_eq (L4YAML.Proofs.ScannerLoopInvariant.advance_indents _)]
    simp [ScannerState.emit, ScannerState.mk', ScannerState.currentIndent]

lemma seed_sound (input : String) :
    L4YAML.Proofs.PendingKeySound.Sound ((ScannerState.mk' input).emit .streamStart) :=
  (L4YAML.Proofs.PendingKeySound.mk'_sound input).of_eq rfl rfl rfl rfl rfl rfl

lemma seed_bom_sound (input : String) :
    L4YAML.Proofs.PendingKeySound.Sound ((ScannerState.mk' input).emit .streamStart).consumeBOM :=
  (seed_sound input).of_eq (L4YAML.Proofs.PendingKeysStable.advance_preserves_pendingKeys _) (L4YAML.Proofs.ScannerLoopInvariant.advance_indents _)
    (L4YAML.Proofs.ScannerCorrectness.advance_preserves_flowLevel _) (L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine _)
    (L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol _) (L4YAML.Proofs.ScannerCorrectness.advance_preserves_explicitKeyStack _)

end L4YAML.Proofs.ColFloor
