import L4YAML.Proofs.Scanner.RegisterWitness

set_option autoImplicit false

namespace L4YAML.Proofs.RegisterWitness
open L4YAML.Scanner
open L4YAML.Proofs.PendingKeySound

-- CANDIDATE: actual closing branch, not a token-only NotQuestionPark claim.
theorem r2_closed_value_excludes_column {s s' : ScannerState} {n : Nat}
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
  simpa only [hcn', h_col] using hc

-- The actual explicit-value discriminator, with the clear's own fields.
theorem r2_explicit_value_excludes_own_column {s s' : ScannerState} {n : Nat}
    (hok : scanValue s = .ok s') (hs : Sound s)
    (h_nf : s.inFlow = false)
    (h_col : (scanValueClearKey s).explicitKeyCol = (n : Int))
    (h_cursor : s.col = n)
    (h_live : (scanValueClearKey s).explicitKeyLine.isSome = true)
    (h_key : (scanValueClearKey s).simpleKey.possible = false) :
    n ∉ markedCols s' := by
  apply r2_closed_value_excludes_column hok hs h_nf _ h_col
  simp [scanValueKeySurvives, h_nf, h_col, h_cursor, h_live, h_key]

#print axioms r2_closed_value_excludes_column
#print axioms r2_explicit_value_excludes_own_column
end L4YAML.Proofs.RegisterWitness
