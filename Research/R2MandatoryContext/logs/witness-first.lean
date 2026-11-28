import Research.R2MandatoryContext.Values
import Research.R2ScannerMapOwnership.JointFixture

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.CharPredicates R2ConcreteSuppliers R2ConcreteSequences
open R2JointFrames R2ActualJointStep

namespace R2MandatoryWitness
open R2MandatoryContext

def source := "? - ? a\n    ? b\n    : c\n  - d\n: e\n"
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

-- All states are obtained from actual initialized successful scanner prefixes.
-- The equalities below are checked inside Lean's kernel, with no default state.
example : scanKey (dispatchState p0) = .ok s1 := by decide +kernel
example : scanBlockEntry (dispatchState p1) = .ok s2 := by decide +kernel
example : scanKey (dispatchState p2) = .ok s3 := by decide +kernel
example : scanKey (dispatchState p4) = .ok s5 := by decide +kernel
example : RegisterWitness.markedCols s3 = [0,4] ∧
    RegisterWitness.markedCols s5 = [0,4] ∧ RegisterWitness.markedCols s7 = [0] := by decide +kernel
example : levels s5 = [FrameLevel.map 4,FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel

lemma first : Slot s1 (SLYamlStream (pos 0 0)) 0 .blockOut (pos 1 1) := by
  simpa only [show (dispatchState p0).col = 0 by decide +kernel] using
    (actual_first_question (s := dispatchState p0) (t := s1)
      (start := pos 0 0) (land := pos 0 0) (q := pos 0 0) (next := pos 1 1)
      (by decide +kernel) (by decide +kernel)
      (show SlotCheck (dispatchState p0) from by unfold SlotCheck; decide +kernel).sound.1
      (show MonoCheck (dispatchState p0) from by unfold MonoCheck; decide +kernel).sound
      (by decide +kernel) rfl (GStar.nil _) (by change SIndent 0 _ _; exact SIndent.zero _)
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

lemma inner : Slot s3 (SLYamlStream (pos 0 0)) 4 .blockOut (pos 5 5) := by
  apply Slot.compact_question (before := dispatchState p2) (n := 2) (m := 1)
    (payload := fun e node => context_dispatch
      (context_preprocess (by decide +kernel : scanNextToken_preprocess s2 = .ok (some (p2,'?')))
        (sequence e node e (SCompactSeqTail.nil 2 e))))
  · decide +kernel
  · decide +kernel
  · intro f mem mark
    have newMarks : RegisterWitness.markedCols s3 = [0,4] := by decide +kernel
    have oldMarks : RegisterWitness.markedCols (dispatchState p2) = [0] := by decide +kernel
    have oldLevels : levels (dispatchState p2) = [FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel
    simp only [oldLevels, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · simp [newMarks] at mark
    · simp [oldMarks]
  · exact SIndent.succ 0 _ 3 _ (SIndent.zero _)
  · exact GLit.mk _ 4

lemma after_a : Context s4 (SLYamlStream (pos 0 0)) (pos 8 0) := by
  apply context_content (prep := p3) (c := 'a') (by decide +kernel) (by decide +kernel)
  exact inner _ (plainAKey 4 5 (source.toList.drop 8))

lemma repeated : Slot s5 (SLYamlStream (pos 0 0)) 4 .blockOut (pos 13 5) := by
  simpa only [show (dispatchState p4).col = 4 by decide +kernel] using
    (actual_same_question (s := dispatchState p4) (t := s5)
      (land := pos 8 0) (q := pos 12 4) (next := pos 13 5)
      (by decide +kernel) (by decide +kernel)
      (show SlotCheck (dispatchState p4) from by unfold SlotCheck; decide +kernel).sound.1
      (show MonoCheck (dispatchState p4) from by unfold MonoCheck; decide +kernel).sound
      (by unfold IndentStackBase.SentinelBase; decide +kernel) (by decide +kernel)
      (context_dispatch (context_preprocess
        (by decide +kernel : scanNextToken_preprocess s4 = .ok (some (p4,'?'))) after_a))
      (by change SIndent 4 _ _; exact SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
        (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero _)))))
      (GLit.mk _ 4))

lemma after_b : Context s6 (SLYamlStream (pos 0 0)) (pos 16 0) := by
  apply context_content (prep := p5) (c := 'b') (by decide +kernel) (by decide +kernel)
  exact repeated _ (SBlockIndented.node 4 .blockOut _ _ (SBlockNode_blockIn_to_blockOut
    (letterNode 5 5 'b' (source.toList.drop 16)
      (by unfold isNsPlainSafe isNsChar; decide) (by decide))))

lemma sound_p6 : Sound (dispatchState p6) := by
  refine ⟨(show SlotCheck (dispatchState p6) from by unfold SlotCheck; decide +kernel).sound.1,
    ?_, ?_, ?_⟩
  · intro _; decide +kernel
  · intro positive
    have zero : (dispatchState p6).flowLevel = 0 := by decide +kernel
    omega
  · unfold StackOk; decide +kernel

lemma value_inner : Slot s7 (SLYamlStream (pos 0 0)) 4 .blockOut (pos 21 5) := by
  have result := explicit_colon (s := dispatchState p6) (t := s7) (line := 1)
    (start := pos 0 0) (e := pos 16 0) (i := pos 20 4) (c := pos 21 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) sound_p6
    (show MonoCheck (dispatchState p6) from by unfold MonoCheck; decide +kernel).sound
    (show SlotCheck (dispatchState p6) from by unfold SlotCheck; decide +kernel).sound.2
    (context_dispatch (context_preprocess
      (by decide +kernel : scanNextToken_preprocess s6 = .ok (some (p6,':'))) after_b))
    (by change SIndent 4 _ _; exact SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
      (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero _))))) (GLit.mk _ 4)
  simpa only [show (dispatchState p6).col = 4 by decide +kernel] using result.1

lemma after_c : Context s8 (SLYamlStream (pos 0 0)) (pos 24 0) := by
  apply context_content (prep := p7) (c := 'c') (by decide +kernel) (by decide +kernel)
  exact value_inner _ (SBlockIndented.node 4 .blockOut _ _ (SBlockNode_blockIn_to_blockOut
    (letterNode 5 5 'c' (source.toList.drop 24)
      (by unfold isNsPlainSafe isNsChar; decide) (by decide))))

lemma sibling : Sequence s9 (SLYamlStream (pos 0 0)) 2 (pos 27 3) := by
  have slot := landed_sequence_context (s := s8) (prep := p8) (t := s9) (k := 2)
    (land := pos 24 0) (dash := pos 26 2) (next := pos 27 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) after_c
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero _)))
    (GLit.mk _ 2) (space_not_ns _ _)
  exact slot_sequence (rest := [FrameLevel.map 0]) (by decide +kernel) slot

lemma after_d : Context s10 (SLYamlStream (pos 0 0)) (pos 30 0) := by
  apply context_content (prep := p9) (c := 'd') (by decide +kernel) (by decide +kernel)
  exact sibling _ (SBlockIndented.node 2 .blockIn _ _
    (letterNode 3 3 'd' (source.toList.drop 30)
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
    (start := pos 0 0) (e := pos 30 0) (i := pos 30 0) (c := pos 31 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) sound_p10
    (show MonoCheck (dispatchState p10) from by unfold MonoCheck; decide +kernel).sound
    (show SlotCheck (dispatchState p10) from by unfold SlotCheck; decide +kernel).sound.2
    (context_dispatch (context_preprocess
      (by decide +kernel : scanNextToken_preprocess s10 = .ok (some (p10,':'))) after_d))
    (by change SIndent 0 _ _; exact SIndent.zero _) (GLit.mk _ 0)
  have value : SBlockIndented (dispatchState p10).col .blockOut (pos 31 1) ⟨[],0⟩ := by
    change SBlockIndented 0 .blockOut _ _
    exact SBlockIndented.node 0 .blockOut _ _ (SBlockNode_blockIn_to_blockOut
      (letterNode 1 1 'e' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  exact (result.1 _ value).close

#print axioms initialized_complete

end R2MandatoryWitness
