import Research.R2MandatoryContext.Births

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.PendingKeysStable
open L4YAML.Proofs.PreprocessIndentStable
open R2JointFrames R2ActualJointStep

namespace R2MandatoryContext

-- This lives before the accumulation invariant in the proposed source. The
-- existing StreamAccum append lemma is declared later and cannot be imported
-- back into its own module.
lemma sequence_tail_append {k : Nat} : ∀ {s m t : SurfPos},
    SCompactSeqTail k s m → SCompactSeqTail k m t → SCompactSeqTail k s t
  | _, _, _, .nil _ _, second => second
  | _, _, _, .cons _ s a b e _ indent literal notNs node first, second =>
      .cons k s a b e _ indent literal notNs node (sequence_tail_append first second)

-- A single actual scanner adapter handles both pushing a new sequence level
-- and keeping the existing level (including an indentless sequence). The old
-- mandatory route is composed before the new scanner layout is projected.
lemma sequence_step {s prep t : ScannerState} {P : SurfPos → Prop}
    {next : SurfPos} {k : Nat}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,'-')))
    (step : scanBlockEntry (dispatchState prep) = .ok t)
    (flow : (dispatchState prep).inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (column : (dispatchState prep).col = k)
    (route : Sequence s P k next) : Sequence t P k next := by
  have prepSound := PendingKeySound.preprocess_sound preprocess sound mono
  have slots : SlotsOk (dispatchState prep) := by
    unfold dispatchState
    split
    · exact prepSound.slots.of_eq rfl rfl
    · exact prepSound.slots
  have back := RegisterWitness.scanBlockEntry_markedCols flow step
    (RegisterWitness.MarkedColsIn.self (dispatchState prep)) slots
  by_cases pushed : (dispatchState prep).currentIndent < ((dispatchState prep).col : Int)
  · have shape := sequence_push step flow pushed
    rw [column] at shape
    intro e node z tail
    change Joint t P (levels t) z
    rw [shape]
    intro finish future
    exact (context_dispatch (context_preprocess preprocess
      (route e node finish (sequence_tail_append tail future)))).restrict_marks
        (fun _ h => back.mem h)
  · have indents : t.indents = (dispatchState prep).indents := by
      rw [scanBlockEntry_indents flow step, pushSequenceIndent, ite_eq_right pushed]
    intro e node z tail
    change Joint t P (levels t) z
    rw [levels_indents indents]
    exact (context_dispatch (context_preprocess preprocess (route e node z tail))).restrict_marks
      (fun _ h => back.mem h)

lemma pair_completion {s : ScannerState} {start next : SurfPos} {k : Nat}
    (old : ∀ e, SBlockIndented k .blockIn next e →
      ∀ z, SCompactSeqTail k e z → SLYamlStream start z ∧
        L4YAML.Proofs.R2ConsumptionClosure.EntryValues s (SLYamlStream start) z)
    (whole : Sequence s (SLYamlStream start) k next) :
    ∀ e, SBlockIndented k .blockIn next e → ∀ z, SCompactSeqTail k e z →
      SLYamlStream start z ∧
        (L4YAML.Proofs.R2ConsumptionClosure.EntryValues s (SLYamlStream start) z ∧
         Context s (SLYamlStream start) z) :=
  fun e node z tail => ⟨(old e node z tail).1,(old e node z tail).2,whole e node z tail⟩

def Completed (s : ScannerState) (P : SurfPos → Prop) (n : Nat) (gram : SurfPos) : Prop :=
  ∀ e, SSLComments gram e → ∀ z, SCompactSeqTail n e z → Context s P z

lemma context_content {s prep t : ScannerState} {P : SurfPos → Prop} {e : SurfPos} {c : Char}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,c)))
    (step : scanNextToken_dispatchContent (dispatchState prep) c = .ok t)
    (context : Context s P e) : Context t P e :=
  context_transport (context_dispatch (context_preprocess preprocess context))
    (dispatchContent_pendingKeys step) (IndentStackBase.dispatchContent_preserves_indents step)

lemma context_flow {s prep t : ScannerState} {P : SurfPos → Prop} {e : SurfPos} {c : Char}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,c)))
    (step : scanNextToken_dispatchFlowIndicators (dispatchState prep) c = .ok (some t))
    (context : Context s P e) : Context t P e :=
  context_transport (context_dispatch (context_preprocess preprocess context))
    (dispatchFlowIndicators_preserves_pendingKeys step)
    (FlowIndentStable.dispatchFlowIndicators_preserves_indents step)

lemma Node.content {s prep t : ScannerState} {P : SurfPos → Prop}
    {old next : SurfPos} {n : Nat} {c : Char}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,c)))
    (step : scanNextToken_dispatchContent (dispatchState prep) c = .ok t)
    (payload : Node s P n old)
    (reader : ∀ e, SBlockNode n .blockIn next e → SBlockNode n .blockIn old e) :
    Node t P n next :=
  fun e node => context_content preprocess step (payload e (reader e node))

lemma Sequence.content {s prep t : ScannerState} {P : SurfPos → Prop}
    {slot gram : SurfPos} {n : Nat} {c : Char}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,c)))
    (step : scanNextToken_dispatchContent (dispatchState prep) c = .ok t)
    (payload : Sequence s P n slot)
    (reader : ∀ e, SSLComments gram e → SBlockIndented n .blockIn slot e) :
    Completed t P n gram :=
  fun e comments z tail => context_content preprocess step (payload e (reader e comments) z tail)

lemma Sequence.flow_close {s prep t : ScannerState} {P : SurfPos → Prop}
    {slot gram : SurfPos} {n : Nat} {c : Char}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,c)))
    (step : scanNextToken_dispatchFlowIndicators (dispatchState prep) c = .ok (some t))
    (payload : Sequence s P n slot)
    (reader : ∀ e, SSLComments gram e → SBlockIndented n .blockIn slot e) :
    Completed t P n gram :=
  fun e comments z tail => context_flow preprocess step (payload e (reader e comments) z tail)

lemma Sequence.properties {s prep t : ScannerState} {P : SurfPos → Prop}
    {slot nodeStart : SurfPos} {n : Nat} {c : Char}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,c)))
    (step : scanNextToken_dispatchContent (dispatchState prep) c = .ok t)
    (payload : Sequence s P n slot)
    (reader : ∀ e, SBlockNode (n+1) .blockIn nodeStart e → SBlockIndented n .blockIn slot e) :
    ∀ e, SBlockNode (n+1) .blockIn nodeStart e →
      ∀ z, SCompactSeqTail n e z → Context t P z :=
  fun e node z tail => context_content preprocess step (payload e (reader e node) z tail)

lemma slot_sequence {s : ScannerState} {P : SurfPos → Prop}
    {rest : List FrameLevel} {next : SurfPos} {k : Nat}
    (shape : levels s = FrameLevel.seq k :: rest) (slot : Slot s P k .blockIn next) :
    Sequence s P k next := by
  intro e node z tail
  have context : Joint s P (FrameLevel.seq k :: rest) e := by
    simpa only [Context, shape] using slot e node
  change Joint s P (levels s) z
  rw [shape]
  exact context.sequence_tail tail

lemma Completed.actual_sibling {s prep t : ScannerState} {P : SurfPos → Prop}
    {gram land dash next : SurfPos} {k : Nat}
    (preprocess : scanNextToken_preprocess s = .ok (some (prep,'-')))
    (step : scanBlockEntry prep = .ok t) (flow : prep.inFlow = false)
    (active : atSequenceIndent prep = true) (column : prep.col = k)
    (payload : Completed s P k gram) (comments : SSLComments gram land)
    (indent : SIndent k land dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    Sequence t P k next := by
  have context := payload land comments land (SCompactSeqTail.nil k land)
  have opened := landed_sequence_context preprocess step flow active column context indent literal notNs
  obtain ⟨rest, shape, _⟩ := sequence_top active
  rw [column] at shape
  exact slot_sequence ((scan_sequence_keeps_levels flow step active).trans shape) opened

lemma actual_nested_sequence {s t : ScannerState} {P : SurfPos → Prop}
    {slot land dash next : SurfPos} {n k : Nat}
    (step : scanBlockEntry s = .ok t) (flow : s.inFlow = false)
    (slots : SlotsOk s) (column : s.col = k)
    (pushed : s.currentIndent < (s.col : Int))
    (payload : Node s P (n+1) slot) (bound : n < k) (comments : SSLComments slot land)
    (indent : SIndent k land dash) (literal : GLit '-' dash next) (notNs : GNot SNsChar next) :
    Sequence t P k next := by
  have shape := sequence_push step flow pushed
  rw [column] at shape
  have back := RegisterWitness.scanBlockEntry_markedCols flow step
    (RegisterWitness.MarkedColsIn.self s) slots
  intro e node z tail
  change Joint t P (levels t) z
  rw [shape]
  intro finish future
  exact (payload finish (nestedBlockSeq bound comments
    (SBlockSeqEntries_of_compactTail indent literal notNs node
      (SCompactSeqTail_append tail future)))).restrict_marks (fun _ h => back.mem h)

#print axioms context_content
#print axioms sequence_step
#print axioms context_flow
#print axioms Node.content
#print axioms Sequence.content
#print axioms Sequence.flow_close
#print axioms Sequence.properties
#print axioms Completed.actual_sibling
#print axioms actual_nested_sequence

end R2MandatoryContext
