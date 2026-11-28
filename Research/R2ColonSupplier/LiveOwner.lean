import L4YAML.Proofs.Production.StreamAccum

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PendingKeySound

namespace R2ColonSupplier

lemma live_register_marked {s : ScannerState} {own : Nat}
    (sound : Sound s) (flow : s.flowLevel = 0)
    (live : s.explicitKeyLine ≠ none) (column : s.explicitKeyCol = (own : Int)) :
    own ∈ RegisterWitness.markedCols s := by
  obtain ⟨line, hline⟩ := Option.ne_none_iff_exists.mp live
  have innermost : PendingKeys.innermost s.indentColumns s.pendingKeys =
      (some line, (own : Int)) := by
    rw [← innermostPendingKey_eq, ← sound.reg flow, hline, column]
  obtain ⟨i, _, marked, getColumn⟩ := innermost_some_mem _ _ _ _ innermost
  obtain ⟨c, atColumn, nonnegative⟩ := sound.slots.2 i line marked
  rw [atColumn] at getColumn
  simp only [Option.getD_some] at getColumn
  exact RegisterWitness.markedCols_mem.mpr ⟨i, line, c, marked, atColumn,
    by rw [getColumn]; exact Int.toNat_natCast own⟩

-- A real live register at the landing came from the actual before-state.
lemma live_landing_marked {before prep : ScannerState} {own : Nat} {c : Char}
    (preprocess : scanNextToken_preprocess before = .ok (some (prep,c)))
    (sound : Sound before) (mono : IndentStackMono.Mono before)
    (noflow : prep.inFlow = false)
    (live : prep.explicitKeyLine ≠ none)
    (column : prep.explicitKeyCol = (own : Int)) :
    own ∈ RegisterWitness.markedCols before := by
  have inPrep := live_register_marked (PendingKeySound.preprocess_sound preprocess sound mono)
    ((inFlow_false_iff prep).1 noflow) live column
  exact (RegisterWitness.preprocess_markedCols preprocess
    (RegisterWitness.MarkedColsIn.self before)).mem inPrep

-- This is exactly the existing colon source split, with no new scanner flag.
def StampSource (prep : ScannerState) : Prop :=
  let dispatch := if prep.allowDirectives then
    { prep with allowDirectives := false, documentEverStarted := true } else prep
  dispatch.explicitKeyLine = none ∨
    (scanValueClearKey dispatch).simpleKey.possible = true ∨
    (dispatch.col : Int) ≠ dispatch.explicitKeyCol

lemma live_landing_of_no_stamp {before prep : ScannerState} {own : Nat}
    (preprocess : scanNextToken_preprocess before = .ok (some (prep, ':')))
    (sound : Sound before) (mono : IndentStackMono.Mono before)
    (noflow : prep.inFlow = false) (atColumn : prep.col = own)
    (source : ¬ StampSource prep) : own ∈ RegisterWitness.markedCols before := by
  apply live_landing_marked preprocess sound mono noflow
  · intro dead
    apply source
    left
    split <;> exact dead
  · have equal : (prep.col : Int) = prep.explicitKeyCol := by
      apply Classical.byContradiction
      intro ne
      apply source
      right; right
      split <;> exact ne
    rw [atColumn] at equal
    exact equal.symm

#print axioms live_register_marked
#print axioms live_landing_marked
#print axioms live_landing_of_no_stamp

end R2ColonSupplier
