import Research.R2ScannerMapOwnership.Bridge
import Research.R2JointFrames.Slots

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.R2ConsumptionClosure

namespace R2ActualJointStep
open R2JointFrames

def frame (e : IndentEntry) : Option FrameLevel :=
  if e.column < 0 then none
  else some (if e.isSequence then FrameLevel.seq e.column.toNat else FrameLevel.map e.column.toNat)

lemma levels_indents {s t : ScannerState} (h : t.indents = s.indents) : levels t = levels s := by
  unfold levels
  rw [h]

lemma levels_push {s t : ScannerState} {e : IndentEntry}
    (h : t.indents = s.indents.push e) : levels t = (frame e).toList ++ levels s := by
  change t.indents.toList.reverse.filterMap frame =
    (frame e).toList ++ s.indents.toList.reverse.filterMap frame
  rw [h, Array.toList_push, List.reverse_append, List.filterMap_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.filterMap_cons, List.filterMap_nil]
  cases hf : frame e <;> rfl

-- Actual unwinding deletes an initial segment of the mixed top-first levels.
-- This is stronger than membership preservation and costs no scanner invariant.
lemma unwind_prefix (s : ScannerState) (col : Int) (fuel : Nat) :
    ∃ pre, levels s = pre ++ levels (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => exact ⟨[], by simp [unwindIndentsLoop]⟩
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · rename_i guard
      have parts : s.currentIndent > col ∧ s.indents.size > 1 := by simpa using guard
      have gt := parts.2
      let popped : ScannerState := { s.emit .blockEnd with
        indents := (s.emit .blockEnd).indents.pop,
        pendingKeys := (s.emit .blockEnd).pendingKeys.pop }
      obtain ⟨pre, old⟩ := ih popped
      have pushed : s.indents = popped.indents.push s.indents.back! :=
        Array.eq_push_pop_back!_of_size_ne_zero (by omega)
      have shape := levels_push pushed
      refine ⟨(frame s.indents.back!).toList ++ pre, ?_⟩
      rw [shape, old, List.append_assoc]
    · exact ⟨[], rfl⟩

lemma stale_indents (s : ScannerState) : (closeStaleExplicitKey s).indents = s.indents := by
  rcases L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_cases s with eq | ⟨_, _, eq⟩
  · rw [eq]
  · rw [eq]; rfl

lemma preprocess_prefix {s t : ScannerState} {c : Char}
    (step : scanNextToken_preprocess s = .ok (some (t,c))) :
    ∃ pre, levels s = pre ++ levels t := by
  unfold scanNextToken_preprocess at step
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at step
  split at step
  · contradiction
  · rename_i skipped skip
    have same : levels skipped = levels s :=
      levels_indents (skipToContent_preserves_indents s skipped skip)
    split at step
    · simp at step
    · split at step
      · split at step
        · contradiction
        · split at step
          · simp at step
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            obtain ⟨pre, shape⟩ := unwind_prefix skipped (skipped.col : Int) skipped.indents.size
            refine ⟨pre, ?_⟩
            rw [← same, shape]
            congr 1
            apply levels_indents
            rw [stale_indents, saveSimpleKey_preserves_indents]
            rfl
      · split at step
        · contradiction
        · split at step
          · simp at step
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            refine ⟨[], ?_⟩
            simp only [List.nil_append]
            rw [← same]
            symm
            apply levels_indents
            rw [stale_indents, saveSimpleKey_preserves_indents]

lemma context_preprocess {s t : ScannerState} {c : Char} {P : SurfPos → Prop} {e : SurfPos}
    (step : scanNextToken_preprocess s = .ok (some (t,c)))
    (context : Context s P e) : Context t P e := by
  obtain ⟨pre, shape⟩ := preprocess_prefix step
  change Joint s P (levels s) e at context
  rw [shape] at context
  exact context.drop.restrict_marks
    (fun _ marked => (RegisterWitness.preprocess_markedCols step
      (RegisterWitness.MarkedColsIn.self s)).mem marked)

lemma context_transport {s t : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (context : Context s P e) (keys : t.pendingKeys = s.pendingKeys)
    (indents : t.indents = s.indents) : Context t P e := by
  change Joint t P (levels t) e
  rw [levels_indents indents]
  exact context.restrict_marks
    (fun _ marked => ((RegisterWitness.MarkedColsIn.self s).transport keys indents).mem marked)

-- This is the scanner's existing flag update between preprocessing and block
-- dispatch. It introduces no new state or independently stored snapshot.
def dispatchState (prep : ScannerState) : ScannerState :=
  if prep.allowDirectives then {prep with allowDirectives := false, documentEverStarted := true}
  else prep

lemma context_dispatch {s : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (context : Context s P e) : Context (dispatchState s) P e := by
  unfold dispatchState
  split
  · exact context_transport context rfl rfl
  · exact context

lemma sequence_top {s : ScannerState} (top : atSequenceIndent s = true) :
    ∃ rest, levels s = FrameLevel.seq s.col :: rest ∧ s.currentIndent = (s.col : Int) := by
  unfold atSequenceIndent at top
  cases back : s.indents.back? with
  | none => simp [back] at top
  | some entry =>
    have parts : entry.isSequence = true ∧ (s.col : Int) = entry.column := by
      simpa only [back, Bool.and_eq_true, beq_iff_eq] using top
    obtain ⟨array, eq⟩ := Array.back?_eq_some_iff.mp back
    let previous : ScannerState := {s with indents := array}
    have pushed : s.indents = previous.indents.push entry := eq
    have shape := levels_push pushed
    refine ⟨levels previous, ?_, ?_⟩
    · simpa [frame, parts.1, ← parts.2, show ¬(s.col : Int) < 0 by omega] using shape
    · simp [ScannerState.currentIndent, back, ← parts.2]

lemma scan_sequence_keeps_levels {s t : ScannerState}
    (flow : s.inFlow = false) (step : scanBlockEntry s = .ok t)
    (top : atSequenceIndent s = true) : levels t = levels s := by
  have shape := scanBlockEntry_indents flow step
  have eq := (sequence_top top).choose_spec.2
  apply levels_indents
  rw [shape]
  unfold pushSequenceIndent
  simp [eq]

lemma landed_sequence_context {s prep t : ScannerState} {P : SurfPos → Prop}
    {land dash next : SurfPos} {k : Nat}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,'-')))
    (step : scanBlockEntry prep = .ok t) (flow : prep.inFlow = false)
    (active : atSequenceIndent prep = true) (column : prep.col = k)
    (context : Context s P land)
    (indent : SIndent k land dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    Slot t P k .blockIn next := by
  have atPrep := context_preprocess preprocess context
  obtain ⟨rest, shape, unchanged⟩ := sequence_top active
  rw [column] at shape
  have resultShape : levels t = FrameLevel.seq k :: rest :=
    (scan_sequence_keeps_levels flow step active).trans shape
  have keys : t.pendingKeys = prep.pendingKeys := by
    rw [scanBlockEntry_pendingKeys flow step]
    unfold pushSequenceIndent
    simp [unchanged]
  have indents : t.indents = prep.indents := by
    rw [scanBlockEntry_indents flow step]
    unfold pushSequenceIndent
    simp [unchanged]
  have back : ∀ x ∈ RegisterWitness.markedCols t, x ∈ RegisterWitness.markedCols prep :=
    fun _ marked => ((RegisterWitness.MarkedColsIn.self prep).transport keys indents).mem marked
  intro e node
  exact atPrep.resume_sequence (pre := []) (by simpa using shape) resultShape back
    indent literal notNs node

-- The existing grammar context is the sole semantic input. Both stack-shape
-- premises of the pure algebra and the marked-domain step are paid by the
-- actual preprocess and actual scanBlockEntry, for arbitrary landing depths.
lemma landed_sequence {s prep t : ScannerState} {start land dash next : SurfPos} {k : Nat}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,'-')))
    (step : scanBlockEntry prep = .ok t) (flow : prep.inFlow = false)
    (active : atSequenceIndent prep = true) (column : prep.col = k)
    (context : Context s (SLYamlStream start) land)
    (mono : IndentStackMono.Mono t) (sound : Sound t) (maps : R2MapOwnership.Maps t)
    (indent : SIndent k land dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    L4YAML.Proofs.R2SequenceContext.SequenceValues t start k next := by
  have atPrep := context_preprocess preprocess context
  obtain ⟨rest, shape, _⟩ := sequence_top active
  rw [column] at shape
  have resultShape : levels t = FrameLevel.seq k :: rest :=
    (scan_sequence_keeps_levels flow step active).trans shape
  have unchanged := (sequence_top active).choose_spec.2
  have keys : t.pendingKeys = prep.pendingKeys := by
    rw [scanBlockEntry_pendingKeys flow step]
    unfold pushSequenceIndent
    simp [unchanged]
  have indents : t.indents = prep.indents := by
    rw [scanBlockEntry_indents flow step]
    unfold pushSequenceIndent
    simp [unchanged]
  have back : ∀ x ∈ RegisterWitness.markedCols t, x ∈ RegisterWitness.markedCols prep :=
    fun _ marked => ((RegisterWitness.MarkedColsIn.self prep).transport keys indents).mem marked
  exact atPrep.landed_sequence (pre := []) (by simpa using shape) resultShape back
    mono sound.slots maps indent literal notNs

lemma initialized_landed_sequence (input : String) (n : Nat)
    {s prep t : ScannerState} {start land dash next : SurfPos} {k : Nat}
    (reached : R2MapOwnership.prefixes input n = some s)
    (wholeStep : scanNextToken s = .ok (some t))
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,'-')))
    (step : scanBlockEntry prep = .ok t) (flow : prep.inFlow = false)
    (active : atSequenceIndent prep = true) (column : prep.col = k)
    (context : Context s (SLYamlStream start) land)
    (indent : SIndent k land dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    L4YAML.Proofs.R2SequenceContext.SequenceValues t start k next := by
  have nextPrefix : R2MapOwnership.prefixes input (n+1) = some t := by
    simp [R2MapOwnership.prefixes, reached, wholeStep]
  obtain ⟨sound, mono, _, _, maps⟩ := R2MapOwnership.initialized_facts input (n+1) t nextPrefix
  exact landed_sequence preprocess step flow active column context mono sound maps indent literal notNs

#print axioms context_preprocess
#print axioms scan_sequence_keeps_levels
#print axioms landed_sequence_context
#print axioms landed_sequence
#print axioms initialized_landed_sequence

end R2ActualJointStep
