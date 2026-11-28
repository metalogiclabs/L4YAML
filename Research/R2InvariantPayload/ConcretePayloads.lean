import Research.R2InvariantPayload.SourceControls
import Research.R2InvariantPayload.NodeValues

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.CharPredicates
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.R2InvariantPayload R2ConcreteSuppliers R2PayloadControls

namespace R2ConcretePayloads

def q : SurfPos := ⟨['?', ' ', 'a', '\n', ':', ' ', 'b', '\n', '?', ' ', 'c', '\n', ':', ' ', 'd', '\n'], 0⟩
def key : SurfPos := ⟨[' ', 'a', '\n', ':', ' ', 'b', '\n', '?', ' ', 'c', '\n', ':', ' ', 'd', '\n'], 1⟩
def keyEnd : SurfPos := ⟨[':', ' ', 'b', '\n', '?', ' ', 'c', '\n', ':', ' ', 'd', '\n'], 0⟩
def value : SurfPos := ⟨[' ', 'b', '\n', '?', ' ', 'c', '\n', ':', ' ', 'd', '\n'], 1⟩

example : q.chars = rootValueSource.toList := by decide +kernel
example : (afterFirstColon rootValueSource).input.toList.drop
    (afterFirstColon rootValueSource).offset = value.chars := by decide +kernel

-- This test supplies an actual block node to the question payload. A compact
-- key control alone would not establish that the node-domain is inhabited.
lemma question_node : SBlockNode 1 .blockIn key keyEnd :=
  letterNode 1 1 'a' keyEnd.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)

lemma root_question_payload : NodeValues (rootQuestion rootValueSource) q 0 key := by
  apply NodeValues.of_question (GLit.mk _ 0 : GLit '?' q key)
  · intro v entry z tail
    exact (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q) (SIndent.zero q)
      v entry z tail).close
  · intro x hx
    simpa [simple_question_marks] using hx

lemma actual_question_context : EntryValues (rootQuestion rootValueSource) (SLYamlStream q) keyEnd :=
  (root_question_payload keyEnd question_node).1

-- The consumed root value keeps its mapping tail, which includes the later
-- sibling `? c : d` in this source. No abstract root route is assumed.
lemma root_value_payload : NodeValues (afterFirstColon rootValueSource) q 0 value := by
  have route : ∀ v, SBlockMapEntry 0 q v →
      ∀ z, SCompactMapTail 0 v z → SLYamlStream q z :=
    fun v entry z tail =>
      (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q) (SIndent.zero q)
        v entry z tail).close
  have step := entryStep_of_question (GLit.mk _ 0 : GLit '?' q key) route
    (plainAKey 0 1 keyEnd.chars)
  apply NodeValues.of_no_marks value_marks
  intro e node z tail
  exact step.2 keyEnd value (SIndent.zero keyEnd) (GLit.mk _ 0) e
    (SBlockIndented.node 0 .blockOut value e
      (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut node)) z tail

def siblingStart : SurfPos := ⟨['?', ' ', 'c', '\n', ':', ' ', 'd', '\n'], 0⟩
def siblingKey : SurfPos := ⟨[' ', 'c', '\n', ':', ' ', 'd', '\n'], 1⟩
def siblingColon : SurfPos := ⟨[':', ' ', 'd', '\n'], 0⟩
def siblingValue : SurfPos := ⟨[' ', 'd', '\n'], 1⟩

lemma value_node : SBlockNode 1 .blockIn value siblingStart :=
  letterNode 1 1 'b' siblingStart.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)

lemma sibling_entry : SBlockMapEntry 0 siblingStart ⟨[], 0⟩ := by
  apply SBlockMapEntry.explicit 0 siblingStart siblingKey siblingColon siblingColon siblingValue ⟨[], 0⟩
  · exact GLit.mk _ 0
  · exact SBlockIndented.node 0 .blockOut _ _
      (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'c' siblingColon.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)))
  · exact SIndent.zero _
  · exact GLit.mk _ 0
  · exact SBlockIndented.node 0 .blockOut _ _
      (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut
        (letterNode 1 1 'd' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)))

-- A real non-nil sibling tail is spent through the stored framed payload.
lemma actual_sibling_tail_consumed : SLYamlStream q ⟨[], 0⟩ := by
  have frame := (root_value_payload siblingStart value_node).2 (by simp [value_marks])
  have tail : SCompactMapTail 0 siblingStart ⟨[], 0⟩ :=
    SCompactMapTail.cons 0 siblingStart siblingStart ⟨[], 0⟩ ⟨[], 0⟩
      (SIndent.zero _) sibling_entry (SCompactMapTail.nil _ _)
  obtain ⟨ks, widths, cont⟩ := frame.resumeAtMap (j := 0) (by simp)
  exact ValuesBelow.close ((cont ⟨[], 0⟩ tail).close)

-- A real ancestor-bearing value park also inhabits the full stored payload.
lemma ancestor_value_payload : NodeValues (afterFirstColon input6) q0_6 6 value6 := by
  have root : ∀ v, SBlockMapEntry 0 q0_6 v →
      ∀ z, SCompactMapTail 0 v z → SLYamlStream q0_6 z :=
    fun v entry z tail =>
      (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q0_6) (SIndent.zero q0_6)
        v entry z tail).close
  have rootKey := fun (e : SurfPos) (h : SBlockIndented 0 .blockOut k0_6 e) =>
    entryStep_of_question (GLit.mk _ 0 : GLit '?' q0_6 k0_6) root h
  have entry1 := compactEntryRoute rootKey
    (SIndent.succ 0 _ 1 q1_6 (SIndent.zero q1_6) : SIndent 1 k0_6 q1_6)
  have key1 := fun (e : SurfPos) (h : SBlockIndented 2 .blockOut k1_6 e) =>
    entryStep_of_question (GLit.mk _ 2 : GLit '?' q1_6 k1_6) entry1 h
  have entry2 := compactEntryRoute key1
    (SIndent.succ 0 _ 3 q2_6 (SIndent.zero q2_6) : SIndent 1 k1_6 q2_6)
  have key2 := fun (e : SurfPos) (h : SBlockIndented 4 .blockOut k2_6 e) =>
    entryStep_of_question (GLit.mk _ 4 : GLit '?' q2_6 k2_6) entry2 h
  have entry3 := compactEntryRoute key2
    (SIndent.succ 0 _ 5 q3_6 (SIndent.zero q3_6) : SIndent 1 k2_6 q3_6)
  have key3 := entryStep_of_question (GLit.mk _ 6 : GLit '?' q3_6 k3_6) entry3
    (plainAKey 6 7 line6)
  have indent : SIndent 6 endKey6 ind6 := by
    exact SIndent.succ 5 _ 0 _ (SIndent.succ 4 _ 1 _ (SIndent.succ 3 _ 2 _
      (SIndent.succ 2 _ 3 _ (SIndent.succ 1 _ 4 _
        (SIndent.succ 0 _ 5 _ (SIndent.zero ind6))))))
  intro e node
  constructor
  · have supplied := colon_value_domain key3 indent (GLit.mk _ 6 : GLit ':' ind6 value6) e node
    simpa [EntryValues, columnCeiling, ValuesBelow, marks6] using supplied
  · intro _
    exact KeyFrames.mapLevel 6 [] e (by simp) (fun z tail => KeyFrames.bottom z (by
      have supplied := key3.2 ind6 value6 indent (GLit.mk _ 6 : GLit ':' ind6 value6) e
        (SBlockIndented.node 6 .blockOut value6 e
          (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut node)) z tail
      simpa [EntryValues, columnCeiling, ValuesBelow, marks6] using supplied))

lemma actual_ancestor_frame :
    KeyFrames (ExplValueLine q0_6 0) [IndentStackCover.FrameLevel.map 6]
      ⟨[' ', ' ', ':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 0⟩ := by
  apply NodeValues.framed_ancestor ancestor_value_payload
  · simp [marks6]
  · simp [marks6]
  · exact letterNode 7 7 'b' _ (by unfold isNsPlainSafe isNsChar; decide) (by decide)

lemma actual_ancestor_stack_mono : IndentStackMono.Mono (afterFirstColon input6) := by
  intro i hi
  have size : (afterFirstColon input6).indents.size = 5 := by decide +kernel
  have bound : i + 1 < 5 := by simpa [size] using hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide +kernel +revert

lemma actual_ancestor_frame_cover :
    IndentStackCover.Floor 6 7 [IndentStackCover.FrameLevel.map 6] ∧
      IndentStackCover.Covered 6 [IndentStackCover.FrameLevel.map 6] (afterFirstColon input6) :=
  own_frame_cover actual_ancestor_stack_mono (by decide +kernel)

#print axioms ancestor_value_payload
#print axioms actual_ancestor_frame
#print axioms actual_ancestor_frame_cover

#print axioms actual_question_context
#print axioms actual_sibling_tail_consumed

#print axioms root_question_payload
#print axioms root_value_payload

end R2ConcretePayloads
