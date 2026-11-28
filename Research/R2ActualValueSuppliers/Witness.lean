import Research.R2ActualValueSuppliers.Producers
import Research.R2ScannerMapOwnership.JointFixture

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.CharPredicates R2ConcreteSuppliers R2ConcreteSequences
open R2JointFrames R2ActualJointStep R2MandatoryContext

namespace R2ActualValueWitness
open R2ActualValueSuppliers

def source := "? - a: b\n    c: d\n  - e\n: f\n"
def pos (offset column : Nat) : SurfPos := ⟨source.toList.drop offset,column⟩
def state (n : Nat) (present : (R2MapOwnership.prefixes source n).isSome = true) : ScannerState :=
  (R2MapOwnership.prefixes source n).get present
def s0 := state 0 (by decide +kernel)
def s1 := state 1 (by decide +kernel)
def s2 := state 2 (by decide +kernel)
def s3 := state 3 (by decide +kernel)
def s4 := state 4 (by decide +kernel)
def s5 := state 5 (by decide +kernel)
def s6 := state 6 (by decide +kernel)
def s7 := state 7 (by decide +kernel)
def s8 := state 8 (by decide +kernel)
def s9 := state 9 (by decide +kernel)
def s10 := state 10 (by decide +kernel)
def s11 := state 11 (by decide +kernel)

def preparation (s : ScannerState)
    (present : ((scanNextToken_preprocess s).toOption.join).isSome = true) : ScannerState :=
  (((scanNextToken_preprocess s).toOption.join).get present).1
def p0 := preparation s0 (by decide +kernel)
def p1 := preparation s1 (by decide +kernel)
def p2 := preparation s2 (by decide +kernel)
def p3 := preparation s3 (by decide +kernel)
def p4 := preparation s4 (by decide +kernel)
def p5 := preparation s5 (by decide +kernel)
def p6 := preparation s6 (by decide +kernel)
def p7 := preparation s7 (by decide +kernel)
def p8 := preparation s8 (by decide +kernel)
def p9 := preparation s9 (by decide +kernel)
def p10 := preparation s10 (by decide +kernel)

-- The same-map colon is at column 5 while the saved key is at column 4.
example : scanValue (dispatchState p6) = .ok s7 := by decide +kernel
example : (dispatchState p6).col = 5 ∧
    (scanValueClearKey (dispatchState p6)).simpleKey.pos.col = 4 := by decide +kernel
example : levels s7 = [FrameLevel.map 4,FrameLevel.seq 2,FrameLevel.map 0] ∧
    RegisterWitness.markedCols s7 = [0] := by decide +kernel

lemma first : Slot s1 (SLYamlStream (pos 0 0)) 0 .blockOut (pos 1 1) := by
  simpa only [show (dispatchState p0).col = 0 by decide +kernel] using
    (actual_first_question (s := dispatchState p0) (t := s1)
      (start := pos 0 0) (land := pos 0 0) (q := pos 0 0) (next := pos 1 1)
      (by decide +kernel) (by decide +kernel)
      (show SlotCheck (dispatchState p0) from by unfold SlotCheck; decide +kernel).sound.1
      (show MonoCheck (dispatchState p0) from by unfold MonoCheck; decide +kernel).sound
      (by decide +kernel) rfl (GStar.nil _)
      (by rw [show (dispatchState p0).col = 0 by decide +kernel]; exact SIndent.zero _)
      (GLit.mk _ 0))

lemma sequence : Sequence s2 (SLYamlStream (pos 0 0)) 2 (pos 3 3) := by
  apply actual_compact_sequence (s := dispatchState p1) (n := 0) (m := 1)
    (step := by decide +kernel) (flow := by decide +kernel)
    (slots := (show SlotCheck (dispatchState p1) from by unfold SlotCheck; decide +kernel).sound.1)
    (column := by decide +kernel) (pushed := by decide +kernel)
    (payload := fun e node => context_dispatch
      (context_preprocess (by decide +kernel : scanNextToken_preprocess s1 = .ok (some (p1,'-')))
        (first e node)))
  · exact SIndent.succ 0 _ 1 _ (SIndent.zero _)
  · exact GLit.mk _ 2
  · exact space_not_ns _ _

lemma sequence_after_key : Slot s3 (SLYamlStream (pos 0 0)) 2 .blockIn (pos 3 3) := by
  intro e node
  exact context_content (s := s2) (prep := p2) (c := 'a') (by decide +kernel) (by decide +kernel)
    (sequence e node e (SCompactSeqTail.nil 2 e))

lemma sound_p3 : Sound (dispatchState p3) := by
  refine ⟨(show SlotCheck (dispatchState p3) from by unfold SlotCheck; decide +kernel).sound.1,
    ?_, ?_, ?_⟩
  · intro _; decide +kernel
  · intro positive
    have zero : (dispatchState p3).flowLevel = 0 := by decide +kernel
    omega
  · unfold StackOk; decide +kernel

lemma first_inner_value : Node s4 (SLYamlStream (pos 0 0)) 5 (pos 6 6) := by
  apply compact_implicit (s := dispatchState p3) (n := 2) (m := 1)
    (slot := pos 3 3) (key := pos 4 4) (colon := pos 5 5)
    (step := by decide +kernel) (flow := by decide +kernel)
    (sound := sound_p3)
    (mono := (show MonoCheck (dispatchState p3) from by unfold MonoCheck; decide +kernel).sound)
    (base := by unfold IndentStackBase.SentinelBase; decide +kernel)
    (possible := by decide +kernel) (column := by decide +kernel) (pushed := by decide +kernel)
    (payload := fun e node => context_dispatch (context_preprocess
      (by decide +kernel : scanNextToken_preprocess s3 = .ok (some (p3,':')))
      (sequence_after_key e node)))
  · exact SIndent.succ 0 _ 3 _ (SIndent.zero _)
  · exact implicitKeyHead_to_SImplicitKey
      (ImplicitKeyHead.yaml (SNsPlainOneLine.mk .blockKey _ _ _
        (SNsPlainFirst.nonIndicator .blockKey 'a' _ 4
          (by unfold isNsPlainSafe isNsChar; decide) (by decide)) (GStar.nil _))) (GStar.nil _)
  · exact GLit.mk _ 5

lemma after_b : Context s5 (SLYamlStream (pos 0 0)) (pos 9 0) := by
  apply context_content (s := s4) (prep := p4) (c := 'b') (by decide +kernel) (by decide +kernel)
  exact first_inner_value _ (letterNode 5 6 'b' (source.toList.drop 9)
    (by unfold isNsPlainSafe isNsChar; decide) (by decide))

lemma after_key_c : Context s6 (SLYamlStream (pos 0 0)) (pos 9 0) :=
  context_content (s := s5) (prep := p5) (c := 'c') (by decide +kernel) (by decide +kernel) after_b

lemma sound_p6 : Sound (dispatchState p6) := by
  refine ⟨(show SlotCheck (dispatchState p6) from by unfold SlotCheck; decide +kernel).sound.1,
    ?_, ?_, ?_⟩
  · intro _; decide +kernel
  · intro positive
    have zero : (dispatchState p6).flowLevel = 0 := by decide +kernel
    omega
  · unfold StackOk; decide +kernel

lemma sibling_inner_value : Node s7 (SLYamlStream (pos 0 0)) 5 (pos 15 6) := by
  apply actual_same_implicit (s := dispatchState p6) (own := 4)
    (land := pos 9 0) (key := pos 13 4) (keyEnd := pos 14 5) (colon := pos 14 5)
    (step := by decide +kernel) (flow := by decide +kernel)
    (sound := sound_p6)
    (mono := (show MonoCheck (dispatchState p6) from by unfold MonoCheck; decide +kernel).sound)
    (base := by unfold IndentStackBase.SentinelBase; decide +kernel)
    (possible := by decide +kernel) (column := by decide +kernel) (same := by decide +kernel)
    (context := context_dispatch (context_preprocess
      (by decide +kernel : scanNextToken_preprocess s6 = .ok (some (p6,':'))) after_key_c))
  · exact SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
      (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero _))))
  · exact ImplicitKeyHead.yaml (SNsPlainOneLine.mk .blockKey _ _ _
      (SNsPlainFirst.nonIndicator .blockKey 'c' _ 4
        (by unfold isNsPlainSafe isNsChar; decide) (by decide)) (GStar.nil _))
  · exact GStar.nil _
  · exact GLit.mk _ 5

lemma after_d : Context s8 (SLYamlStream (pos 0 0)) (pos 18 0) := by
  apply context_content (s := s7) (prep := p7) (c := 'd') (by decide +kernel) (by decide +kernel)
  exact sibling_inner_value _ (letterNode 5 6 'd' (source.toList.drop 18)
    (by unfold isNsPlainSafe isNsChar; decide) (by decide))

lemma sibling : Sequence s9 (SLYamlStream (pos 0 0)) 2 (pos 21 3) := by
  have slot := landed_sequence_context (s := s8) (prep := p8) (t := s9) (k := 2)
    (land := pos 18 0) (dash := pos 20 2) (next := pos 21 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) after_d
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero _)))
    (GLit.mk _ 2) (space_not_ns _ _)
  exact slot_sequence (rest := [FrameLevel.map 0]) (by decide +kernel) slot

lemma after_e : Context s10 (SLYamlStream (pos 0 0)) (pos 24 0) := by
  apply context_content (s := s9) (prep := p9) (c := 'e') (by decide +kernel) (by decide +kernel)
  exact sibling _ (SBlockIndented.node 2 .blockIn _ _
    (letterNode 3 3 'e' (source.toList.drop 24)
      (by unfold isNsPlainSafe isNsChar; decide) (by decide))) _ (SCompactSeqTail.nil 2 _)

lemma sound_p10 : Sound (dispatchState p10) := by
  refine ⟨(show SlotCheck (dispatchState p10) from by unfold SlotCheck; decide +kernel).sound.1,
    ?_, ?_, ?_⟩
  · intro _; decide +kernel
  · intro positive
    have zero : (dispatchState p10).flowLevel = 0 := by decide +kernel
    omega
  · unfold StackOk; decide +kernel

lemma initialized_complete : SLYamlStream (pos 0 0) ⟨[],0⟩ := by
  have result := explicit_colon (s := dispatchState p10) (t := s11) (line := 0)
    (start := pos 0 0) (e := pos 24 0) (i := pos 24 0) (c := pos 25 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) sound_p10
    (show MonoCheck (dispatchState p10) from by unfold MonoCheck; decide +kernel).sound
    (show SlotCheck (dispatchState p10) from by unfold SlotCheck; decide +kernel).sound.2
    (context_dispatch (context_preprocess
      (by decide +kernel : scanNextToken_preprocess s10 = .ok (some (p10,':'))) after_e))
    (by rw [show (dispatchState p10).col = 0 by decide +kernel]; exact SIndent.zero _) (GLit.mk _ 0)
  have value : SBlockIndented (dispatchState p10).col .blockOut (pos 25 1) ⟨[],0⟩ := by
    rw [show (dispatchState p10).col = 0 by decide +kernel]
    exact SBlockIndented.node 0 .blockOut _ _ (SBlockNode_blockIn_to_blockOut
      (letterNode 1 1 'f' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  exact (result.1 _ value).close

#print axioms initialized_complete

end R2ActualValueWitness
