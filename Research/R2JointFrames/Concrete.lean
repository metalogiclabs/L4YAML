import Research.R2JointFrames.Slots
import Research.R2SequenceContext.ConcreteContexts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.CharPredicates R2ConcreteSuppliers R2CompactControls
open R2SequenceControls R2ConcreteSequences

namespace R2JointConcrete
open R2JointFrames

def source : String := mixed
def rootState : ScannerState := questionState source 0
def sequenceState : ScannerState := dashState source 0
def innerState : ScannerState := questionState source 1
def consumedState : ScannerState := afterFirstColon source
def siblingState : ScannerState := dashState source 1
def finalState : ScannerState := (nthColon source 1).getD (ScannerState.mk' source)

def q0 : SurfPos := ⟨source.toList,0⟩
def k0 : SurfPos := ⟨source.toList.drop 1,1⟩
def dash2 : SurfPos := ⟨source.toList.drop 2,2⟩
def seqSlot : SurfPos := ⟨source.toList.drop 3,3⟩
def q4 : SurfPos := ⟨source.toList.drop 4,4⟩
def k4 : SurfPos := ⟨source.toList.drop 5,5⟩
def endA : SurfPos := ⟨[' ',' ',' ',' ',':',' ','b','\n',' ',' ','-',' ','c','\n',':',' ','d','\n'],0⟩
def colon4 : SurfPos := ⟨endA.chars.drop 4,4⟩
def value4 : SurfPos := ⟨endA.chars.drop 5,5⟩
def endB : SurfPos := ⟨[' ',' ','-',' ','c','\n',':',' ','d','\n'],0⟩
def nextDash : SurfPos := ⟨endB.chars.drop 2,2⟩
def nextSlot : SurfPos := ⟨endB.chars.drop 3,3⟩
def endC : SurfPos := ⟨[':',' ','d','\n'],0⟩
def value0 : SurfPos := ⟨[' ','d','\n'],1⟩

lemma rootLevels : levels rootState = [FrameLevel.map 0] := by decide +kernel
lemma sequenceLevels : levels sequenceState = [FrameLevel.seq 2, FrameLevel.map 0] := by decide +kernel
lemma innerLevels : levels innerState = [FrameLevel.map 4,FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel
lemma consumedLevels : levels consumedState = [FrameLevel.map 4,FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel
lemma siblingLevels : levels siblingState = [FrameLevel.seq 2,FrameLevel.map 0] := by decide +kernel
lemma finalLevels : levels finalState = [FrameLevel.map 0] := by decide +kernel
lemma rootMarks : RegisterWitness.markedCols rootState = [0] := by decide +kernel
lemma sequenceMarks : RegisterWitness.markedCols sequenceState = [0] := by decide +kernel
lemma innerMarks : RegisterWitness.markedCols innerState = [0,4] := by decide +kernel
lemma consumedMarks : RegisterWitness.markedCols consumedState = [0] := by decide +kernel
lemma siblingMarks : RegisterWitness.markedCols siblingState = [0] := by decide +kernel
lemma finalMarks : RegisterWitness.markedCols finalState = [] := by decide +kernel

example : (nthQuestion source 1).isSome = true ∧ (nthColon source 1).isSome = true := by decide +kernel
example : consumedState.input.toList.drop consumedState.offset = value4.chars := by decide +kernel
example : siblingState.input.toList.drop siblingState.offset = nextSlot.chars := by decide +kernel

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
  · simp [sequenceLevels, rootLevels]
  · intro f hf marked
    simpa [sequenceMarks, rootMarks] using marked
  · exact SIndent.succ 0 _ 1 dash2 (SIndent.zero dash2)
  · exact GLit.mk _ 2
  · exact space_not_ns _ _

lemma inner_context : Slot innerState (SLYamlStream q0) 4 .blockOut k4 := by
  apply Slot.compact_question (n := 2) (m := 1) sequence_context
  · simp [innerLevels, sequenceLevels]
  · simp [innerMarks]
  · intro f hf marked
    simp only [sequenceLevels, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · simp [innerMarks] at marked
    · simp [sequenceMarks]
  · exact SIndent.succ 0 _ 3 q4 (SIndent.zero q4)
  · exact GLit.mk _ 4

lemma inner_key : Context innerState (SLYamlStream q0) endA :=
  inner_context endA (plainAKey 4 5 endA.chars)

lemma consumed_inner : Context consumedState (SLYamlStream q0) endB := by
  have key := inner_key
  change Joint innerState (SLYamlStream q0) (levels innerState) endA at key
  rw [innerLevels] at key
  change Joint consumedState (SLYamlStream q0) (levels consumedState) endB
  rw [consumedLevels]
  apply key.consume (by simp [innerMarks]) (by simp [consumedMarks])
    (by intro x hx; simp only [consumedMarks, List.mem_singleton] at hx; simp [hx,innerMarks])
    (SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
      (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero colon4)))))
    (GLit.mk _ 4 : GLit ':' colon4 value4)
  exact SBlockIndented.node 4 .blockOut value4 endB
    (SBlockNode_blockIn_to_blockOut
      (letterNode 5 5 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

lemma sibling_content : SBlockIndented 2 .blockIn nextSlot endC :=
  SBlockIndented.node 2 .blockIn nextSlot endC
    (letterNode 3 3 'c' endC.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide))

lemma sibling_context : Context siblingState (SLYamlStream q0) endC := by
  apply consumed_inner.resume_sequence (pre := [FrameLevel.map 4]) (rest := [FrameLevel.map 0])
    (by simp [consumedLevels]) (by simp [siblingLevels])
    (by intro x hx; simpa [siblingMarks,consumedMarks] using hx)
    (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero nextDash)))
    (GLit.mk _ 2 : GLit '-' nextDash nextSlot) (space_not_ns _ _) sibling_content

lemma sibling_slot_check : SlotCheck siblingState := by unfold SlotCheck; decide +kernel
lemma sibling_mono_check : MonoCheck siblingState := by unfold MonoCheck; decide +kernel

lemma actual_landed_family :
    L4YAML.Proofs.R2SequenceContext.SequenceValues siblingState q0 2 nextSlot := by
  apply consumed_inner.landed_sequence (pre := [FrameLevel.map 4]) (rest := [FrameLevel.map 0])
    (by simp [consumedLevels]) (by simp [siblingLevels])
    (by intro x hx; simpa [siblingMarks,consumedMarks] using hx)
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

#print axioms root_context
#print axioms consumed_inner
#print axioms sibling_context
#print axioms initialized_complete
#print axioms actual_landed_family

end R2JointConcrete
