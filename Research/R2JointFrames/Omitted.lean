import Research.R2JointFrames.Concrete

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.CharPredicates R2ConcreteSuppliers R2CompactControls
open R2SequenceControls R2ConcreteSequences

namespace R2JointOmitted
open R2JointFrames

def source : String := "? - ? a\n  - c\n: d\n"
def rootState : ScannerState := questionState source 0
def sequenceState : ScannerState := dashState source 0
def innerState : ScannerState := questionState source 1
def siblingState : ScannerState := dashState source 1
def finalState : ScannerState := afterFirstColon source
def q0 : SurfPos := ⟨source.toList,0⟩
def k0 : SurfPos := ⟨source.toList.drop 1,1⟩
def dash2 : SurfPos := ⟨source.toList.drop 2,2⟩
def seqSlot : SurfPos := ⟨source.toList.drop 3,3⟩
def q4 : SurfPos := ⟨source.toList.drop 4,4⟩
def k4 : SurfPos := ⟨source.toList.drop 5,5⟩
def endA : SurfPos := ⟨[' ',' ','-',' ','c','\n',':',' ','d','\n'],0⟩
def nextDash : SurfPos := ⟨endA.chars.drop 2,2⟩
def nextSlot : SurfPos := ⟨endA.chars.drop 3,3⟩
def endC : SurfPos := ⟨[':',' ','d','\n'],0⟩
def value0 : SurfPos := ⟨[' ','d','\n'],1⟩

lemma rootLevels : levels rootState = [FrameLevel.map 0] := by decide +kernel
lemma sequenceLevels : levels sequenceState = [FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel
lemma innerLevels : levels innerState = [FrameLevel.map 4,FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel
lemma siblingLevels : levels siblingState = [FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel
lemma rootMarks : RegisterWitness.markedCols rootState = [0] := by decide +kernel
lemma sequenceMarks : RegisterWitness.markedCols sequenceState = [0] := by decide +kernel
lemma innerMarks : RegisterWitness.markedCols innerState = [0,4] := by decide +kernel
lemma siblingMarks : RegisterWitness.markedCols siblingState = [0] := by decide +kernel
lemma finalMarks : RegisterWitness.markedCols finalState = [] := by decide +kernel

#guard (L4YAML.TokenParser.parseYaml source).isOk
example : (nthQuestion source 1).isSome = true ∧ (nthDash source 1).isSome = true := by decide +kernel

lemma root_context : Slot rootState (SLYamlStream q0) 0 .blockOut k0 := by
  intro e key
  change Joint rootState (SLYamlStream q0) (levels rootState) e
  rw [rootLevels]
  apply Joint.question (by simp [rootMarks]) (GLit.mk _ 0 : GLit '?' q0 k0) ?_ key
  intro v entry z tail
  exact (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q0) (SIndent.zero q0)
    v entry z tail).close

lemma sequence_context : Slot sequenceState (SLYamlStream q0) 2 .blockIn seqSlot := by
  apply Slot.compact_sequence (n := 0) (m := 1) root_context
  · simp [sequenceLevels,rootLevels]
  · intro f hf marked; simpa [sequenceMarks,rootMarks] using marked
  · exact SIndent.succ 0 _ 1 dash2 (SIndent.zero dash2)
  · exact GLit.mk _ 2
  · exact space_not_ns _ _

lemma inner_context : Slot innerState (SLYamlStream q0) 4 .blockOut k4 := by
  apply Slot.compact_question (n := 2) (m := 1) sequence_context
  · simp [innerLevels,sequenceLevels]
  · simp [innerMarks]
  · intro f hf marked
    simp only [sequenceLevels,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl | rfl
    · simp [innerMarks] at marked
    · simp [sequenceMarks]
  · exact SIndent.succ 0 _ 3 q4 (SIndent.zero q4)
  · exact GLit.mk _ 4

lemma inner_key : Context innerState (SLYamlStream q0) endA :=
  inner_context endA (plainAKey 4 5 endA.chars)

-- The marked width-4 entry is popped using its omitted-value arm. The
-- width-2 sequence then resumes with a real sibling and width 0 survives.
lemma sibling_context : Context siblingState (SLYamlStream q0) endC := by
  apply inner_key.resume_sequence (pre := [FrameLevel.map 4]) (rest := [FrameLevel.map 0])
    (by simp [innerLevels]) (by simp [siblingLevels])
    (by intro x hx; simp only [siblingMarks,List.mem_singleton] at hx; simp [hx,innerMarks])
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero nextDash)))
    (GLit.mk _ 2 : GLit '-' nextDash nextSlot) (space_not_ns _ _)
  exact SBlockIndented.node 2 .blockIn nextSlot endC
    (letterNode 3 3 'c' endC.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide))

lemma sibling_slot_check : SlotCheck siblingState := by unfold SlotCheck; decide +kernel
lemma sibling_mono_check : MonoCheck siblingState := by unfold MonoCheck; decide +kernel

lemma actual_landed_family :
    L4YAML.Proofs.R2SequenceContext.SequenceValues siblingState q0 2 nextSlot := by
  apply inner_key.landed_sequence (pre := [FrameLevel.map 4]) (rest := [FrameLevel.map 0])
    (by simp [innerLevels]) (by simp [siblingLevels])
    (by intro x hx; simp only [siblingMarks,List.mem_singleton] at hx; simp [hx,innerMarks])
    sibling_mono_check.sound sibling_slot_check.sound.1 sibling_slot_check.sound.2
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero nextDash)))
    (GLit.mk _ 2 : GLit '-' nextDash nextSlot) (space_not_ns _ _)

lemma initialized_complete : SLYamlStream q0 ⟨[],0⟩ := by
  have sibling := sibling_context
  change Joint siblingState (SLYamlStream q0) (levels siblingState) endC at sibling
  rw [siblingLevels] at sibling
  have root := sibling.pop
  have consumed : Joint finalState (SLYamlStream q0) [FrameLevel.map 0] ⟨[],0⟩ := by
    apply root.consume (by simp [siblingMarks]) (by simp [finalMarks])
      (by intro x hx; simp [finalMarks] at hx) (SIndent.zero endC)
      (GLit.mk _ 0 : GLit ':' endC value0)
    exact SBlockIndented.node 0 .blockOut value0 ⟨[],0⟩
      (SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  exact consumed.close

#print axioms sibling_context
#print axioms initialized_complete
#print axioms actual_landed_family

end R2JointOmitted
