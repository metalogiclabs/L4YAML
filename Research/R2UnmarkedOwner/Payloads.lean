import Research.R2UnmarkedOwner.AncestorValue
import Research.R2CompactSlot.SlotValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2InvariantPayload
open L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.IndentStackCover (FrameLevel)

namespace R2UnmarkedOwner

lemma AncestorValue.payloads {sc : ScannerState} {start slot : SurfPos} {own : Nat}
    (route : ∀ e, SBlockIndented own .blockOut slot e → AncestorValue sc start own e)
    (smaller : ∀ x ∈ RegisterWitness.markedCols sc, x < own) :
    SlotValues sc start own .blockOut slot ∧ NodeValues sc start own slot := by
  have retained : ∀ e, SBlockIndented own .blockOut slot e →
      ∀ z, SCompactMapTail own e z → EntryValues sc (SLYamlStream start) z :=
    fun e value z tail => (route e value).2 z tail |>.truncate (ceiling_le_of_marks_lt smaller)
  refine ⟨fun e value => retained e value e (SCompactMapTail.nil own e), ?_⟩
  intro e node
  have value := SBlockIndented.node own .blockOut slot e (SBlockNode_blockIn_to_blockOut node)
  refine ⟨retained e value e (SCompactMapTail.nil own e), ?_⟩
  intro _
  exact KeyFrames.mapLevel own [] e (by simp) (fun z tail => KeyFrames.bottom z (retained e value z tail))

#print axioms AncestorValue.payloads

end R2UnmarkedOwner
