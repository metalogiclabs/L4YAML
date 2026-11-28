import L4YAML.Proofs.Scanner.RegisterWitness

set_option autoImplicit false
set_option maxHeartbeats 2000000
open L4YAML L4YAML.Scanner L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.PendingKeysStable

namespace R2ValueOwnership

def TopUnmarked (s : ScannerState) : Prop :=
  ∀ l, s.pendingKeys.back? ≠ some (some l)

lemma last_mark_register {s : ScannerState} {l : Nat}
    (hs : SlotsOk s) (hr : RegOk s) (hfl : s.flowLevel = 0)
    (marked : s.pendingKeys.back? = some (some l)) :
    s.explicitKeyLine = some l ∧ s.explicitKeyCol = s.currentIndent := by
  have size_ne : s.pendingKeys.size ≠ 0 := by
    intro h
    have empty : s.pendingKeys = #[] := Array.eq_empty_of_size_eq_zero h
    simp [empty] at marked
  have nonempty : 0 < s.pendingKeys.size := by omega
  have sizes := hs.1
  have indnonempty : 0 < s.indents.size := by omega
  have reg := hr hfl
  rw [innermostPendingKey_eq, innermost_eq_go] at reg
  have sz : s.pendingKeys.size = (s.pendingKeys.size - 1) + 1 := by omega
  rw [sz] at reg
  simp only [go] at reg
  have atLast : s.pendingKeys[s.pendingKeys.size - 1]?.getD none = some l := by
    rw [← Array.back?_eq_getElem?]
    simp [marked]
  rw [atLast] at reg
  have cols : s.indentColumns[s.pendingKeys.size - 1]?.getD (-1) = s.currentIndent := by
    rw [hs.1]
    simp only [ScannerState.indentColumns, Array.getElem?_map,
      ScannerState.currentIndent, Array.back?_eq_getElem?]
    cases s.indents[s.indents.size - 1]? <;> rfl
  rw [cols] at reg
  exact Prod.mk.inj reg

lemma prepared_last_mark {s : ScannerState} {l : Nat}
    (hs : Sound s) (hfl : s.inFlow = false)
    (marked : (scanValuePrepare s).pendingKeys.back? = some (some l)) :
    s.explicitKeyLine = some l ∧
      s.explicitKeyCol = (scanValuePrepare s).currentIndent ∧
      (s.simpleKey.possible = true → (s.simpleKey.pos.col : Int) ≤ s.explicitKeyCol) := by
  obtain ⟨slots, inner, flow, line, col, _⟩ := scanValuePrepare_core s hs.slots
  have reg : RegOk (scanValuePrepare s) := by
    intro hz
    rw [line, col, inner]
    exact hs.reg (by rw [← flow]; exact hz)
  have prepflow : (scanValuePrepare s).flowLevel = 0 := by
    rw [flow]
    exact (inFlow_false_iff s).1 hfl
  obtain ⟨hl, hc⟩ := last_mark_register slots reg prepflow marked
  rw [line] at hl
  rw [col] at hc
  refine ⟨hl, hc, ?_⟩
  intro key
  have mark := marked
  simp only [scanValuePrepare, key, hfl, Bool.not_false, ite_true] at mark
  split at mark
  · simp at mark
  · rename_i le
    have eq : (scanValuePrepare s).currentIndent = s.currentIndent := by
      simp only [scanValuePrepare, key, hfl, Bool.not_false, ite_true, ite_eq_right le]
      rfl
    rw [eq] at hc
    omega

lemma last_column {s : ScannerState} {l : Nat} (slots : SlotsOk s)
    (marked : s.pendingKeys.back? = some (some l)) :
    s.indentColumns[s.pendingKeys.size - 1]? = some s.currentIndent := by
  have nonempty : 0 < s.pendingKeys.size := by
    have hget : s.pendingKeys[s.pendingKeys.size - 1]? = some (some l) := by
      simpa only [Array.back?_eq_getElem?] using marked
    obtain ⟨h, _⟩ := Array.getElem?_eq_some_iff.mp hget
    omega
  have positive : 0 < s.indents.size := by have := slots.1; omega
  rw [slots.1, IndentStackMono.currentIndent_eq_last positive]
  simp [ScannerState.indentColumns, Array.getElem?_eq_getElem (by omega :
    s.indents.size - 1 < s.indents.size)]

lemma scanValue_top_unmarked {s s' : ScannerState}
    (hok : scanValue s = .ok s') (hs : Sound s) (hfl : s.inFlow = false) :
    TopUnmarked s' := by
  obtain ⟨ckind, ckpk, ckflow, ckline, ckcol, ckstack⟩ := scanValueClearKey_core s
  have kcSound : Sound (scanValueClearKey s) :=
    hs.of_eq ckpk ckind ckflow ckline ckcol ckstack
  have kcflow : (scanValueClearKey s).inFlow = false := by
    simpa [ScannerState.inFlow, ckflow] using hfl
  have noSurvive {l : Nat}
      (marked : (scanValuePrepare (scanValueClearKey s)).pendingKeys.back? = some (some l)) :
      scanValueKeySurvives s (scanValueClearKey s) ≠ true := by
    obtain ⟨line, col, keyBound⟩ := prepared_last_mark kcSound kcflow marked
    intro survives
    unfold scanValueKeySurvives at survives
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at survives
    rcases survives with ⟨_, dead | ⟨_, gt⟩⟩
    · simp [line] at dead
    · by_cases key : (scanValueClearKey s).simpleKey.possible = true
      · simp only [key, ite_true] at gt
        have := keyBound key
        omega
      · have noKey : (scanValueClearKey s).simpleKey.possible = false := by simpa using key
        simp only [noKey, Bool.false_eq_true, ite_false] at gt
        have oldLine : s.explicitKeyLine = some l := ckline ▸ line
        have actual := (ExplicitKeyCoupling.scanValue_explicit_at_indent hok hfl oldLine noKey).2
        have prepIndent : (scanValuePrepare (scanValueClearKey s)).currentIndent = s.currentIndent := by
          simp [scanValuePrepare, noKey, line, ScannerState.currentIndent, ckind]
        rw [prepIndent] at col
        omega
  have core := scanValuePrepare_core (scanValueClearKey s) kcSound.slots
  have advPk : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys =
      (scanValuePrepare (scanValueClearKey s)).pendingKeys := by
    rw [advance_preserves_pendingKeys, emit_pendingKeys]
  have advInd : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents =
      (scanValuePrepare (scanValueClearKey s)).indents := by
    rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]; rfl
  have advCols : (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indentColumns =
      (scanValuePrepare (scanValueClearKey s)).indentColumns := by
    simp [ScannerState.indentColumns, advInd]
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok
  subst hok
  intro l marked
  simp only [hfl, Bool.false_eq_true, ite_false] at marked
  by_cases survives : scanValueKeySurvives s (scanValueClearKey s) = true
  · simp only [survives, ite_true] at marked
    change (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys.back? = _ at marked
    rw [advPk] at marked
    exact noSurvive marked survives
  · simp only [survives] at marked
    change (PendingKeys.closeAt _ _ (scanValueClearKey s).explicitKeyCol).back? = _ at marked
    rw [Array.back?_eq_getElem?, closeAt_size] at marked
    obtain ⟨old, different⟩ := closeAt_marked _ _ _ _ _ marked
    have oldBack : (scanValuePrepare (scanValueClearKey s)).pendingKeys.back? = some (some l) := by
      simpa only [Array.back?_eq_getElem?, advPk] using old
    obtain ⟨_, col, _⟩ := prepared_last_mark kcSound kcflow oldBack
    apply different
    rw [advCols, advPk, col]
    exact last_column core.1 oldBack

lemma no_mark_at_or_above_top {s : ScannerState} {own : Nat}
    (unmarked : TopUnmarked s) (slots : SlotsOk s)
    (mono : IndentStackMono.Mono s) (top : s.currentIndent ≤ (own : Int)) :
    own ∉ RegisterWitness.markedCols s := by
  intro marked
  obtain ⟨i, l, c, key, column, eq⟩ := RegisterWitness.markedCols_mem.mp marked
  obtain ⟨size, _⟩ := Array.getElem?_eq_some_iff.mp key
  have isize : i < s.indents.size := by rw [← slots.1]; exact size
  have entryColumn : (s.indents[i]'isize).column = c := by
    simpa [ScannerState.indentColumns, Array.getElem?_eq_getElem isize] using column
  obtain ⟨cc, ccColumn, nonnegative⟩ := slots.2 i l key
  have same : cc = c := Option.some.inj (ccColumn.symm.trans column)
  subst cc
  have natColumn : (own : Int) = c := by
    rw [← eq]
    exact Int.toNat_of_nonneg nonnegative
  have below := mono.le_currentIndent (s.indents[i]'isize)
    (Array.mem_iff_getElem.mpr ⟨i, isize, rfl⟩)
  have noNext : ¬ i + 1 < s.indents.size := by
    intro next
    have strictly := mono i next
    have nextBelow := mono.le_currentIndent (s.indents[i + 1]'next)
      (Array.mem_iff_getElem.mpr ⟨i + 1, next, rfl⟩)
    omega
  have last : i = s.pendingKeys.size - 1 := by have := slots.1; omega
  apply unmarked l
  rw [Array.back?_eq_getElem?, ← last]
  exact key

lemma scanValue_own_unmarked {s s' : ScannerState} {own : Nat}
    (hok : scanValue s = .ok s') (hs : Sound s) (hfl : s.inFlow = false)
    (mono : IndentStackMono.Mono s') (top : s'.currentIndent ≤ (own : Int)) :
    own ∉ RegisterWitness.markedCols s' :=
  no_mark_at_or_above_top (scanValue_top_unmarked hok hs hfl)
    (scanValue_sound hok hs).slots mono top

#print axioms last_mark_register
#print axioms prepared_last_mark
#print axioms scanValue_top_unmarked
#print axioms scanValue_own_unmarked

end R2ValueOwnership
