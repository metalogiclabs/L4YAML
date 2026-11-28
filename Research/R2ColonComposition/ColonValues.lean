import Research.R2CompactSlot.SlotValues
import Research.R2ValueOwnership.Ownership

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2InvariantPayload
open L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.IndentStackCover (FrameLevel)

namespace R2ColonComposition

-- An explicit-entry route need not infer ownership from a token flag. The
-- scanner's before-state domain is retained inside the entry's own step.
lemma colon_payload_of_step {before after : ScannerState}
    {start keyEnd ind slot : SurfPos} {own : Nat}
    (step : EntryStep (ValuesBelow before (SLYamlStream start) own) own keyEnd)
    (back : ∀ x < own, x ∈ RegisterWitness.markedCols after →
      x ∈ RegisterWitness.markedCols before)
    (smaller : ∀ x ∈ RegisterWitness.markedCols after, x < own)
    (indent : SIndent own keyEnd ind) (literal : GLit ':' ind slot) :
    SlotValues after start own .blockOut slot ∧ NodeValues after start own slot := by
  have retained : ∀ e, SBlockIndented own .blockOut slot e →
      ∀ z, SCompactMapTail own e z → EntryValues after (SLYamlStream start) z := by
    intro e content z tail
    exact ValuesBelow.restrict (step.2 ind slot indent literal e content z tail) back
      |>.truncate (ceiling_le_of_marks_lt smaller)
  refine ⟨fun e content => retained e content e (SCompactMapTail.nil own e), ?_⟩
  intro e node
  have content := SBlockIndented.node own .blockOut slot e
    (SBlockNode_blockIn_to_blockOut node)
  refine ⟨retained e content e (SCompactMapTail.nil own e), ?_⟩
  intro _
  exact KeyFrames.mapLevel own [] e (by simp) (fun z tail =>
    KeyFrames.bottom z (retained e content z tail))

-- The output retains every smaller ancestor and the consumed map's entire
-- sibling tail. No empty-domain or enclosing-route premise is introduced.
lemma colon_payload {before after : ScannerState} {start keyEnd ind slot : SurfPos}
    {own : Nat} (entries : EntryValues before (SLYamlStream start) keyEnd)
    (ownMark : own ∈ RegisterWitness.markedCols before)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (smaller : ∀ x ∈ RegisterWitness.markedCols after, x < own)
    (indent : SIndent own keyEnd ind) (literal : GLit ':' ind slot) :
    SlotValues after start own .blockOut slot ∧ NodeValues after start own slot := by
  exact colon_payload_of_step (entries.at ownMark (marked_lt_ceiling ownMark))
    (fun x _ hx => back x hx) smaller indent literal

-- This is the real scanner/grammar composition: the successful scanValue
-- supplies own exclusion; the stored family supplies ancestor meaning.
lemma scanValue_payload {before dispatch after : ScannerState}
    {start keyEnd ind slot : SurfPos} {own : Nat}
    (entries : EntryValues before (SLYamlStream start) keyEnd)
    (ownMark : own ∈ RegisterWitness.markedCols before)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (scan : scanValue dispatch = .ok after) (sound : PendingKeySound.Sound dispatch)
    (noflow : dispatch.inFlow = false) (mono : IndentStackMono.Mono after)
    (top : after.currentIndent ≤ (own : Int))
    (indent : SIndent own keyEnd ind) (literal : GLit ':' ind slot) :
    SlotValues after start own .blockOut slot ∧ NodeValues after start own slot := by
  have noOwn := R2ValueOwnership.scanValue_own_unmarked scan sound noflow mono top
  exact colon_payload entries ownMark back (fun x hx => by
    have le := markedCols_le_of_top mono top x hx
    have ne : x ≠ own := fun eq => noOwn (eq ▸ hx)
    omega) indent literal

#print axioms colon_payload
#print axioms colon_payload_of_step
#print axioms scanValue_payload

end R2ColonComposition
