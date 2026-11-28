import Research.R2ScannerMapOwnership.JointStep
import Research.R2ValueOwnership.Ownership

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.R2InvariantPayload

namespace R2ActualJointStep
open R2JointFrames

lemma marked_top_levels {s : ScannerState} {own : Nat}
    (slots : SlotsOk s) (mono : IndentStackMono.Mono s) (maps : R2MapOwnership.Maps s)
    (top : s.currentIndent ≤ (own : Int)) (marked : own ∈ RegisterWitness.markedCols s) :
    ∃ rest, levels s = FrameLevel.map own :: rest := by
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
  have noNext : ¬i + 1 < s.indents.size := by
    intro next
    have strictly := mono i next
    have nextBelow := mono.le_currentIndent (s.indents[i+1]'next)
      (Array.mem_iff_getElem.mpr ⟨i+1,next,rfl⟩)
    omega
  have last : i = s.indents.size-1 := by omega
  obtain ⟨entry, atEntry, kind⟩ := maps i l key
  have actualEntry : entry = s.indents[i]'isize := by
    simpa only [Array.getElem?_eq_getElem isize, Option.some.injEq] using atEntry.symm
  have back : s.indents.back? = some entry := by
    rw [Array.back?_eq_getElem?, ← last]
    exact atEntry
  obtain ⟨array, arrayEq⟩ := Array.back?_eq_some_iff.mp back
  let previous : ScannerState := {s with indents := array}
  have shape := levels_push (s := previous) arrayEq
  refine ⟨levels previous, ?_⟩
  have columnEq : entry.column = (own : Int) := by rw [actualEntry, entryColumn, natColumn]
  simpa [frame, columnEq, kind, show ¬(own : Int) < 0 by omega] using shape

lemma live_register_marked {s : ScannerState} {line : Nat}
    (sound : Sound s) (flow : s.inFlow = false) (key : s.explicitKeyLine = some line)
    (column : (s.col : Int) = s.explicitKeyCol) : s.col ∈ RegisterWitness.markedCols s := by
  have inner : PendingKeys.innermost s.indentColumns s.pendingKeys = (some line, (s.col : Int)) := by
    rw [← innermostPendingKey_eq, ← sound.reg ((inFlow_false_iff s).1 flow), key, column]
  obtain ⟨i, _, atKey, atColumn⟩ := innermost_some_mem _ _ _ _ inner
  obtain ⟨c, columnEq, _⟩ := sound.slots.2 i line atKey
  rw [columnEq, Option.getD_some] at atColumn
  exact RegisterWitness.markedCols_mem.mpr ⟨i,line,(s.col : Int),atKey,
    atColumn ▸ columnEq, by simp⟩

lemma explicit_value_indents {s t : ScannerState} {line : Nat}
    (step : scanValue s = .ok t) (key : s.explicitKeyLine = some line)
    (cleared : (scanValueClearKey s).simpleKey.possible = false) : t.indents = s.indents := by
  have same := scanValueClearKey_core s
  unfold scanValue at step
  simp only [bind, Except.bind] at step
  split at step <;> try contradiction
  split at step <;> try contradiction
  split at step <;> try contradiction
  simp only [Except.ok.injEq] at step
  subst t
  change (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).indents = s.indents
  rw [L4YAML.Proofs.ScannerLoopInvariant.advance_indents]
  change (scanValuePrepare (scanValueClearKey s)).indents = s.indents
  simp [scanValuePrepare, cleared, same.2.2.2.1, key, same.1]

-- The actual explicit-colon producer retains the whole mixed continuation,
-- including every intervening collection tail. Its state shape, owner mark,
-- consumed mark and marked-domain transport are all derived from the scanner.
lemma explicit_colon {s t : ScannerState} {line : Nat} {start e i c : SurfPos}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (key : s.explicitKeyLine = some line)
    (cleared : (scanValueClearKey s).simpleKey.possible = false)
    (column : (s.col : Int) = s.explicitKeyCol)
    (sound : Sound s) (mono : IndentStackMono.Mono s) (maps : R2MapOwnership.Maps s)
    (context : Context s (SLYamlStream start) e)
    (indent : SIndent s.col e i) (literal : GLit ':' i c) :
    Slot t (SLYamlStream start) s.col .blockOut c ∧ NodeValues t start s.col c := by
  have atIndent := (ExplicitKeyCoupling.scanValue_explicit_at_indent step flow key cleared).2
  have marked := live_register_marked sound flow key column
  obtain ⟨rest, oldShape⟩ := marked_top_levels sound.slots mono maps (by omega) marked
  have indents := explicit_value_indents step key cleared
  have newShape : levels t = FrameLevel.map s.col :: rest := (levels_indents indents).trans oldShape
  have newMono := mono.of_indents_eq indents
  have newSound := scanValue_sound step sound
  have newMaps := maps.scan_value step
  have consumed := R2ValueOwnership.scanValue_own_unmarked (own := s.col) step sound flow newMono
    (by rw [currentIndent_of_indents_eq indents]; omega)
  have back : ∀ x ∈ RegisterWitness.markedCols t, x ∈ RegisterWitness.markedCols s :=
    fun _ marked => (RegisterWitness.scanValue_markedCols step
      (RegisterWitness.MarkedColsIn.self s) sound.slots).mem marked
  have slot : Slot t (SLYamlStream start) s.col .blockOut c := by
    intro v value
    change Joint t (SLYamlStream start) (levels t) v
    rw [newShape]
    have before : Joint s (SLYamlStream start) (FrameLevel.map s.col :: rest) e := by
      simpa only [Context, oldShape] using context
    exact before.consume marked consumed back indent literal value
  exact ⟨slot, slot.nodes newShape newMono newSound.slots newMaps⟩

#print axioms live_register_marked
#print axioms explicit_colon

-- Exact initialized, preprocessed and dispatched caller. Structural premises
-- come from initialized_facts and the real scanner transitions. The sole
-- unfinished semantic supply is the retained Context at the completed key.
lemma initialized_explicit_colon (input : String) (n : Nat)
    {s prep t : ScannerState} {line : Nat} {start e i c : SurfPos}
    (reached : R2MapOwnership.prefixes input n = some s)
    (wholeStep : scanNextToken s = .ok (some t))
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,':')))
    (step : scanValue (dispatchState prep) = .ok t)
    (flow : (dispatchState prep).inFlow = false)
    (key : (dispatchState prep).explicitKeyLine = some line)
    (cleared : (scanValueClearKey (dispatchState prep)).simpleKey.possible = false)
    (column : ((dispatchState prep).col : Int) = (dispatchState prep).explicitKeyCol)
    (context : Context s (SLYamlStream start) e)
    (indent : SIndent (dispatchState prep).col e i) (literal : GLit ':' i c) :
    Slot t (SLYamlStream start) (dispatchState prep).col .blockOut c ∧
    NodeValues t start (dispatchState prep).col c ∧
    (∀ v, SBlockIndented (dispatchState prep).col .blockOut c v →
      SLYamlStream start v ∧ L4YAML.Proofs.R2ConsumptionClosure.EntryValues t (SLYamlStream start) v) := by
  obtain ⟨sound, mono, _, _, maps⟩ := R2MapOwnership.initialized_facts input n s reached
  have prepSound := PendingKeySound.preprocess_sound preprocess sound mono
  have prepMono := IndentStackMono.preprocess_mono preprocess mono
  have prepMaps := maps.preprocess sound.slots preprocess
  have disSound : Sound (dispatchState prep) := by
    unfold dispatchState
    split
    · exact prepSound.of_eq rfl rfl rfl rfl rfl rfl
    · exact prepSound
  have disMono : IndentStackMono.Mono (dispatchState prep) := by
    unfold dispatchState
    split
    · exact prepMono.of_indents_eq rfl
    · exact prepMono
  have disMaps : R2MapOwnership.Maps (dispatchState prep) := by
    unfold dispatchState
    split
    · exact prepMaps.of_eq rfl rfl
    · exact prepMaps
  have disContext := context_dispatch (context_preprocess preprocess context)
  obtain ⟨slot, nodes⟩ := explicit_colon step flow key cleared column disSound disMono disMaps
    disContext indent literal
  have nextPrefix : R2MapOwnership.prefixes input (n+1) = some t := by
    simp [R2MapOwnership.prefixes, reached, wholeStep]
  obtain ⟨newSound, newMono, _, _, newMaps⟩ :=
    R2MapOwnership.initialized_facts input (n+1) t nextPrefix
  refine ⟨slot, nodes, ?_⟩
  intro v value
  have retained := slot v value
  exact ⟨retained.close, retained.entries newMono newSound.slots newMaps⟩

#print axioms initialized_explicit_colon

end R2ActualJointStep
