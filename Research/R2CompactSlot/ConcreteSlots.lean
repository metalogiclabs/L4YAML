import Research.R2CompactSlot.Controls
import Research.R2CompactSlot.SlotValues

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.R2InvariantPayload L4YAML.Proofs.R2CompactSlot
open L4YAML.CharPredicates R2CompactControls R2ConcreteSuppliers

namespace R2ConcreteSlots

lemma root_slot : SlotValues (questionState input6 0) q0_6 0 .blockOut k0_6 := by
  apply SlotValues.of_question (GLit.mk _ 0 : GLit '?' q0_6 k0_6)
  · intro v entry z tail
    exact (nodocMapRouteF (k := 0) (by rfl) (GStar.nil q0_6) (SIndent.zero q0_6)
      v entry z tail).close
  · intro x hx
    simpa [marks0] using hx

lemma compact_level1 :
    SlotValues (questionState input6 1) q0_6 2 .blockOut k1_6 ∧
      NodeValues (questionState input6 1) q0_6 2 k1_6 := by
  apply SlotValues.compact_question root_slot
    (SIndent.succ 0 _ 1 q1_6 (SIndent.zero q1_6) : SIndent 1 k0_6 q1_6)
    (GLit.mk _ 2 : GLit '?' q1_6 k1_6)
  · intro x hx
    simp only [marks0, marks1, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega
  · intro x hx
    simp only [marks0, List.mem_singleton] at hx
    omega

lemma compact_level2 :
    SlotValues (questionState input6 2) q0_6 4 .blockOut k2_6 ∧
      NodeValues (questionState input6 2) q0_6 4 k2_6 := by
  apply SlotValues.compact_question compact_level1.1
    (SIndent.succ 0 _ 3 q2_6 (SIndent.zero q2_6) : SIndent 1 k1_6 q2_6)
    (GLit.mk _ 4 : GLit '?' q2_6 k2_6)
  · intro x hx
    simp only [marks1, marks2, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega
  · intro x hx
    simp only [marks1, List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

lemma compact_level3 :
    SlotValues (questionState input6 3) q0_6 6 .blockOut k3_6 ∧
      NodeValues (questionState input6 3) q0_6 6 k3_6 := by
  apply SlotValues.compact_question compact_level2.1
    (SIndent.succ 0 _ 5 q3_6 (SIndent.zero q3_6) : SIndent 1 k2_6 q3_6)
    (GLit.mk _ 6 : GLit '?' q3_6 k3_6)
  · intro x hx
    simp only [marks2, marks3, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    omega
  · intro x hx
    simp only [marks2, List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

-- This wide slot was built from the root through all three compact questions.
lemma actual_deep_key : EntryValues (questionState input6 3) (SLYamlStream q0_6) endKey6 :=
  compact_level3.1 endKey6 (plainAKey 6 7 line6)

-- Consume the actual inner value, omit the column-4 entry, then consume the
-- column-2 and root values. No assumed enclosing route supplies this family.
lemma actual_root_to_consumption : SLYamlStream q0_6 ⟨[], 0⟩ := by
  let middle : List Char := [' ', ' ', ':', ' ', 'd', '\n', ':', ' ', 'e', '\n']
  have indent6 : SIndent 6 endKey6 ind6 := by
    exact SIndent.succ 5 _ 0 _ (SIndent.succ 4 _ 1 _ (SIndent.succ 3 _ 2 _
      (SIndent.succ 2 _ 3 _ (SIndent.succ 1 _ 4 _
        (SIndent.succ 0 _ 5 _ (SIndent.zero ind6))))))
  have bNode := letterNode 7 7 'b' middle (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have afterB : EntryValues (afterFirstColon input6) (SLYamlStream q0_6) ⟨middle, 0⟩ :=
    EntryValues.consume actual_deep_key (by simp [marks3])
      (by intro x hx; simp only [marks6, marks3, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)
      (by intro x hx; simp only [marks6, List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
      indent6 (GLit.mk _ 6) (SBlockIndented.node 6 .blockOut _ _
        (NodeProduction.SBlockNode_blockIn_to_blockOut bNode))
  have indent2 : SIndent 2 ⟨middle, 0⟩ ⟨[':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 2⟩ :=
    SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero _))
  have colon2 : GLit ':' ⟨[':', ' ', 'd', '\n', ':', ' ', 'e', '\n'], 2⟩
      ⟨[' ', 'd', '\n', ':', ' ', 'e', '\n'], 3⟩ := GLit.mk _ 2
  have dNode := letterNode 3 3 'd' [':', ' ', 'e', '\n']
    (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have afterD : EntryValues secondState6 (SLYamlStream q0_6) ⟨[':', ' ', 'e', '\n'], 0⟩ :=
    EntryValues.consume afterB (by simp [marks6])
      (by intro x hx; simp only [marks6second, List.mem_singleton] at hx; subst x; simp [marks6])
      (by intro x hx; simp only [marks6second, List.mem_singleton] at hx; omega)
      indent2 colon2 (SBlockIndented.node 2 .blockOut _ _
        (NodeProduction.SBlockNode_blockIn_to_blockOut dNode))
  have eNode := letterNode 1 1 'e' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have afterE : EntryValues thirdState6 (SLYamlStream q0_6) ⟨[], 0⟩ :=
    EntryValues.consume afterD (by simp [marks6second])
      (by simp [marks6third]) (by simp [marks6third])
      (SIndent.zero _) (GLit.mk _ 0) (SBlockIndented.node 0 .blockOut _ _
        (NodeProduction.SBlockNode_blockIn_to_blockOut eNode))
  exact ValuesBelow.close afterE

#print axioms compact_level3
#print axioms actual_deep_key
#print axioms actual_root_to_consumption

end R2ConcreteSlots
