import L4YAML.Proofs.Scanner.RegisterWitness

set_option autoImplicit false

namespace L4YAML.Proofs.RegisterWitness
open L4YAML.Scanner
open L4YAML.Proofs.PendingKeySound

-- Capstone chain: these actual scanner facts fund pendingMapValue's slot
-- through accum_block_pending -> scanNextToken_accum_step ->
-- scan_content_gives_stream_v2 -> parse_strict_proof. Integration is separate.
-- Actual closing branch, rather than token-only NotQuestionPark.
lemma r2_closed_value_excludes_column {s s' : ScannerState} {n : Nat}
    (hok : scanValue s = .ok s') (hs : Sound s)
    (h_nf : s.inFlow = false)
    (h_close : scanValueKeySurvives s (scanValueClearKey s) = false)
    (h_col : (scanValueClearKey s).explicitKeyCol = (n : Int)) :
    n ∉ markedCols s' := by
  have hs' := scanValue_sound hok hs
  intro hm
  obtain ⟨i, l, c, hi, hc, hcn⟩ := markedCols_mem.mp hm
  obtain ⟨c', hc', hnn⟩ := hs'.slots.2 i l hi
  have hcc : c = c' := Option.some.inj (hc.symm.trans hc')
  have hcn' : c = (n : Int) := by omega
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok
  subst hok
  simp only [h_nf, h_close, Bool.false_eq_true, ↓reduceIte] at hi
  have hne := (closeAt_marked _ _ _ _ _ hi).2
  apply hne
  simpa only [ScannerState.indentColumns, hcn', h_col] using hc

-- The actual explicit-value discriminator, with the clear's own fields.
lemma r2_explicit_value_excludes_own_column {s s' : ScannerState} {n : Nat}
    (hok : scanValue s = .ok s') (hs : Sound s)
    (h_nf : s.inFlow = false)
    (h_col : (scanValueClearKey s).explicitKeyCol = (n : Int))
    (h_cursor : s.col = n)
    (h_live : (scanValueClearKey s).explicitKeyLine.isSome = true)
    (h_key : (scanValueClearKey s).simpleKey.possible = false) :
    n ∉ markedCols s' := by
  apply r2_closed_value_excludes_column hok hs h_nf _ h_col
  simp [scanValueKeySurvives, h_nf, h_col, h_cursor, h_live, h_key]

-- Every successful block value leaves its own mapping column unmarked.
-- This includes implicit sources; a token-only discriminator is insufficient.
lemma r2_prepare_currentIndent_ge (s : ScannerState) :
    s.currentIndent ≤ (scanValuePrepare s).currentIndent := by
  unfold scanValuePrepare
  split
  · split
    · split
      · simpa [ScannerState.currentIndent] using (Int.le_of_lt (by assumption))
      · exact Int.le_refl _
    · exact Int.le_refl _
  · split
    · exact Int.le_refl _
    · split
      · unfold pushMappingIndent
        split
        · simpa [ScannerState.currentIndent, ScannerState.emit] using
            (Int.le_of_lt (by assumption))
        · exact Int.le_refl _
      · exact Int.le_refl _

lemma r2_prepare_key_col_le {s : ScannerState}
    (h_nf : s.inFlow = false) (h_key : s.simpleKey.possible = true) :
    (s.simpleKey.pos.col : Int) ≤ (scanValuePrepare s).currentIndent := by
  unfold scanValuePrepare
  simp only [h_key, h_nf, Bool.not_false, ↓reduceIte]
  split
  · simp [ScannerState.currentIndent]
  · rename_i hle
    change (s.simpleKey.pos.col : Int) ≤ s.currentIndent
    omega

lemma r2_value_currentIndent {s s' : ScannerState}
    (hok : scanValue s = .ok s') :
    s'.currentIndent = (scanValuePrepare (scanValueClearKey s)).currentIndent := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok
  subst hok
  change (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).currentIndent = _
  apply L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq
  rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]
  rfl

lemma r2_value_excludes_top_column {s s' : ScannerState} {n : Nat}
    (hok : scanValue s = .ok s') (hs : Sound s)
    (hm : L4YAML.Proofs.IndentStackMono.Mono s)
    (h_nf : s.inFlow = false) (h_top : s'.currentIndent = (n : Int)) :
    n ∉ markedCols s' := by
  intro hn
  have hnold := (scanValue_markedCols hok (MarkedColsIn.self s) hs.slots).mem hn
  obtain ⟨i, l, c, hi, hc, hcn⟩ := markedCols_mem.mp hnold
  obtain ⟨c', hc', hc0⟩ := hs.slots.2 i l hi
  have hcc : c = c' := Option.some.inj (hc.symm.trans hc')
  have hcn' : c = (n : Int) := by omega
  have hfl : s.flowLevel = 0 := (inFlow_false_iff s).1 h_nf
  have hr := hs.reg hfl
  have hle := marked_le_innermost hs.slots hm i l hi
  rw [hc, Option.getD_some, ← hr] at hle
  have hlive : ∃ ek, s.explicitKeyLine = some ek := by
    cases hek : s.explicitKeyLine with
    | some ek => exact ⟨ek, rfl⟩
    | none =>
      have hf : (PendingKeys.innermost s.indentColumns s.pendingKeys).1 = none := by
        rw [← innermostPendingKey_eq, ← hr, hek]
      have hd := innermost_none_snd s.indentColumns s.pendingKeys hf
      rw [← innermostPendingKey_eq, ← hr] at hd
      omega
  obtain ⟨ek, hek⟩ := hlive
  have hrTop : s.explicitKeyCol ≤ s.currentIndent := by
    have hinn : PendingKeys.innermost s.indentColumns s.pendingKeys =
        (some ek, s.explicitKeyCol) := by
      rw [← innermostPendingKey_eq, ← hr, hek]
    obtain ⟨j, _, hj, hcolj⟩ := innermost_some_mem _ _ _ _ hinn
    obtain ⟨cj, hcj, _⟩ := hs.slots.2 j ek hj
    rw [hcj, Option.getD_some] at hcolj
    simp only [ScannerState.indentColumns, Array.getElem?_map, Option.map_eq_some_iff] at hcj
    obtain ⟨e, he, hec⟩ := hcj
    have hbound := hm.le_currentIndent e (Array.mem_of_getElem? he)
    omega
  obtain ⟨hcol, hind, hflow, _, hekl, hline, _⟩ :=
    L4YAML.Proofs.PreprocessIndentStable.scanValueClearKey_fields s
  have hci : (scanValueClearKey s).currentIndent = s.currentIndent :=
    L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq hind
  have hge := r2_prepare_currentIndent_ge (scanValueClearKey s)
  have htop' := r2_value_currentIndent hok
  have heq : s.explicitKeyCol = (n : Int) := by omega
  have holdtop : s.currentIndent = (n : Int) := by omega
  have hkc : (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol :=
    L4YAML.Proofs.ExplicitKeyCoupling.scanValueClearKey_preserves_explicitKeyCol s
  have hclose : scanValueKeySurvives s (scanValueClearKey s) = false := by
    cases hsk : (scanValueClearKey s).simpleKey.possible with
    | true =>
      have hkbound := r2_prepare_key_col_le (by rw [hflow]; exact h_nf) hsk
      have hkcol : ((scanValueClearKey s).simpleKey.pos.col : Int) ≤
          (scanValueClearKey s).explicitKeyCol := by omega
      simp [scanValueKeySurvives, h_nf, hekl, hek, hsk, hkcol, not_lt_of_ge hkcol]
    | false =>
      have hcursor := (L4YAML.Proofs.ExplicitKeyCoupling.scanValue_explicit_at_indent
        hok h_nf hek hsk).2
      have hcur : (s.col : Int) = (scanValueClearKey s).explicitKeyCol := by omega
      simp [scanValueKeySurvives, h_nf, hekl, hek, hsk, hcur]
  exact r2_closed_value_excludes_column hok hs h_nf hclose (hkc.trans heq) hn

open Lean Elab Command
run_cmd do
  for n in [`L4YAML.Proofs.RegisterWitness.r2_closed_value_excludes_column,
      `L4YAML.Proofs.RegisterWitness.r2_explicit_value_excludes_own_column,
      `L4YAML.Proofs.RegisterWitness.r2_value_excludes_top_column] do
    let axs ← liftCoreM (collectAxioms n)
    for a in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "unexpected axiom {a} in {n}"

#print axioms r2_closed_value_excludes_column
#print axioms r2_explicit_value_excludes_own_column
#print axioms r2_value_excludes_top_column
end L4YAML.Proofs.RegisterWitness
