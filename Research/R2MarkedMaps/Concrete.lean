import Research.R2MarkedMaps.Producers
import Research.R2JointFrames.Concrete

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.CharPredicates R2ConcreteSuppliers R2JointConcrete R2JointFrames

namespace R2ActualProducers

-- Executable equality is local to this research module; no scanner type or
-- production instance is edited. All decisions below use the kernel.
deriving instance DecidableEq for IndentEntry
deriving instance DecidableEq for SimpleKeyState
deriving instance DecidableEq for Positioned
deriving instance DecidableEq for ScannerState
deriving instance DecidableEq for Except

-- Every get is guarded by a kernel proof of an actually returned state.
-- No default state is substituted for a missing scanner event.
def questionPair : ScannerState × Char :=
  ((scanNextToken_preprocess sequenceState).toOption.join).get (by decide +kernel)
def questionPrep : ScannerState := questionPair.1
def scannedKey : ScannerState :=
  ((scanNextToken innerState).toOption.join).get (by decide +kernel)
def colonPair : ScannerState × Char :=
  ((scanNextToken_preprocess scannedKey).toOption.join).get (by decide +kernel)
def colonPrep : ScannerState := colonPair.1

example : questionPair.2 = '?' ∧ colonPair.2 = ':' := by decide +kernel
example : scanKey questionPrep = .ok innerState := by decide +kernel
example : scanValue colonPrep = .ok consumedState := by decide +kernel
example : RegisterWitness.markedCols colonPrep = [0,4] ∧
    RegisterWitness.markedCols consumedState = [0] := by decide +kernel

lemma actual_question_slot : Slot innerState (SLYamlStream q0) 4 .blockOut k4 := by
  apply Slot.actual_question (n := 2) (m := 1) (s := questionPrep)
    (by decide +kernel) (by decide +kernel)
    (show SlotCheck questionPrep from by unfold SlotCheck; decide +kernel).sound.1
    (show MonoCheck questionPrep from by unfold MonoCheck; decide +kernel).sound
    (by unfold IndentStackBase.SentinelBase; decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (sequence_context.of_eq (by decide +kernel) (by decide +kernel))
    (SIndent.succ 0 _ 3 q4 (SIndent.zero q4)) (GLit.mk _ 4 : GLit '?' q4 k4)

lemma actual_key_context : Context colonPrep (SLYamlStream q0) endA :=
  (actual_question_slot endA (plainAKey 4 5 endA.chars)).of_eq
    (by decide +kernel) (by decide +kernel)

lemma colon_sound : Sound colonPrep := by
  refine ⟨(show SlotCheck colonPrep from by unfold SlotCheck; decide +kernel).sound.1,
    ?_, ?_, ?_⟩
  · intro _; decide +kernel
  · intro positive
    have zero : colonPrep.flowLevel = 0 := by decide +kernel
    omega
  · unfold StackOk; decide +kernel

lemma actual_colon_context : Context consumedState (SLYamlStream q0) endB := by
  apply Context.actual_colon (s := colonPrep) (own := 4) (line := 0)
    (rest := [FrameLevel.seq 2,FrameLevel.map 0])
    (by decide +kernel) colon_sound
    (show MonoCheck colonPrep from by unfold MonoCheck; decide +kernel).sound
    (by unfold IndentStackBase.SentinelBase; decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) actual_key_context
    (SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
      (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero colon4)))))
    (GLit.mk _ 4 : GLit ':' colon4 R2JointConcrete.value4)
  exact SBlockIndented.node 4 .blockOut R2JointConcrete.value4 endB
    (SBlockNode_blockIn_to_blockOut
      (letterNode 5 5 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

lemma actual_sibling_context : Context siblingState (SLYamlStream q0) endC := by
  exact actual_colon_context.resume_sequence
    (pre := [FrameLevel.map 4]) (rest := [FrameLevel.map 0])
    (by simp [consumedLevels]) (by simp [siblingLevels])
    (by intro x hx; simpa [siblingMarks,consumedMarks] using hx)
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero nextDash)))
    (GLit.mk _ 2 : GLit '-' nextDash nextSlot) (R2ConcreteSequences.space_not_ns _ _) sibling_content

lemma initialized_complete : SLYamlStream q0 ⟨[],0⟩ := by
  have sibling := actual_sibling_context
  change Joint siblingState (SLYamlStream q0) (levels siblingState) endC at sibling
  rw [siblingLevels] at sibling
  have root := sibling.pop
  have final : Joint finalState (SLYamlStream q0) [FrameLevel.map 0] ⟨[],0⟩ := by
    apply root.consume (by simp [siblingMarks]) (by simp [finalMarks])
      (by intro x hx; simp [finalMarks] at hx) (SIndent.zero endC)
      (GLit.mk _ 0 : GLit ':' endC value0)
    exact SBlockIndented.node 0 .blockOut value0 ⟨[],0⟩
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  exact final.close

#print axioms actual_question_slot
#print axioms actual_colon_context
#print axioms initialized_complete

end R2ActualProducers
