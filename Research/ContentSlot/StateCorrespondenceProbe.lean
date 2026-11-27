module
public import L4YAML.Proofs.Scanner.RegisterWitness
public section
namespace L4YAML.Proofs.StreamAccum
open L4YAML.Scanner
lemma marked_col_of_explicit_source {sc s_prep : ScannerState} {c : Char}
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_sound : PendingKeySound.Sound sc)
    (h_mono : IndentStackMono.Mono sc)
    (h_noflow : s_prep.inFlow = false)
    (h_src : ¬ ((if s_prep.allowDirectives then
        {s_prep with allowDirectives := false, documentEverStarted := true}
      else s_prep).explicitKeyLine = none ∨
      (scanValueClearKey (if s_prep.allowDirectives then
        {s_prep with allowDirectives := false, documentEverStarted := true}
      else s_prep)).simpleKey.possible = true ∨
      ((if s_prep.allowDirectives then
        {s_prep with allowDirectives := false, documentEverStarted := true}
      else s_prep).col : Int) ≠ (if s_prep.allowDirectives then
        {s_prep with allowDirectives := false, documentEverStarted := true}
      else s_prep).explicitKeyCol)) :
    s_prep.col ∈ RegisterWitness.markedCols sc := by
  have hs := PendingKeySound.preprocess_sound h_preprocess h_sound h_mono
  have hfl : s_prep.flowLevel = 0 := by simpa [ScannerState.inFlow] using h_noflow
  have hne : s_prep.explicitKeyLine ≠ none := by
    intro h
    apply h_src
    exact Or.inl (by split <;> exact h)
  have hcol : s_prep.explicitKeyCol = (s_prep.col : Int) := by
    apply Eq.symm
    apply Classical.not_not.mp
    intro h
    apply h_src
    exact Or.inr (Or.inr (by split <;> exact h))
  cases hekl : s_prep.explicitKeyLine with
  | none => exact (hne hekl).elim
  | some l =>
    have hinn : PendingKeys.innermost s_prep.indentColumns s_prep.pendingKeys =
        (some l, (s_prep.col : Int)) := by
      rw [← PendingKeySound.innermostPendingKey_eq, ← hs.reg hfl, hekl, hcol]
    obtain ⟨i, _, hi, hc⟩ := PendingKeySound.innermost_some_mem _ _ _ _ hinn
    obtain ⟨ci, hci, _⟩ := hs.slots.2 i l hi
    rw [hci] at hc
    simp only [Option.getD_some] at hc
    have hm : s_prep.col ∈ RegisterWitness.markedCols s_prep :=
      RegisterWitness.markedCols_mem.mpr ⟨i, l, ci, hi, hci, by omega⟩
    exact (RegisterWitness.preprocess_markedCols h_preprocess
      (RegisterWitness.MarkedColsIn.self sc)).mem hm
#print axioms marked_col_of_explicit_source
end L4YAML.Proofs.StreamAccum

namespace L4YAML.Proofs.StreamAccum
open L4YAML.Scanner
example {sc : ScannerState} {P : Nat → Prop}
    (h_sound : PendingKeySound.Sound sc) (h_fl : sc.flowLevel = 0)
    (h_dead : sc.explicitKeyLine = none) :
    ∃ ns : List Nat, RegisterWitness.MarkedColsIn sc ns ∧ ∀ nv ∈ ns, P nv :=
  ⟨[], RegisterWitness.MarkedColsIn.of_explicitKeyLine_none h_sound h_fl h_dead,
    fun _ hm => absurd hm List.not_mem_nil⟩
end L4YAML.Proofs.StreamAccum
