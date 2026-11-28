import Research.R2ColonComposition.Controls
import Research.R2ColonComposition.ColonValues

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.R2ConsumptionClosure L4YAML.Proofs.R2InvariantPayload
open L4YAML.Proofs.R2CompactSlot
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.CharPredicates
open R2ConcreteSuppliers R2CompactControls R2JointSibling

namespace R2ColonCompositionConcrete

def afterKey : ScannerState :=
  ((scanNextToken (questionState source 1)).toOption.bind id).getD (ScannerState.mk' source)
def prepared : ScannerState :=
  (((scanNextToken_preprocess afterKey).toOption.bind id).map Prod.fst).getD afterKey
def dispatch : ScannerState :=
  if prepared.allowDirectives then
    { prepared with allowDirectives := false, documentEverStarted := true }
  else prepared

def valueOut : ScannerState := (scanValue dispatch).toOption.getD (ScannerState.mk' source)

lemma actual_scan : scanValue dispatch = .ok valueOut := by
  have success : (scanValue dispatch).isOk = true := by decide +kernel
  cases result : scanValue dispatch with
  | error e =>
    rw [result] at success
    change false = true at success
    contradiction
  | ok out => simp only [valueOut, result, Except.toOption, Option.getD]

example : RegisterWitness.markedCols valueOut = [0] := by decide +kernel
example : valueOut.offset = 9 ∧ valueOut.col = 3 := by decide +kernel
example : dispatch.pendingKeys = #[none, some 0, some 0] := by decide +kernel
example : dispatch.inFlow = false := by decide +kernel

lemma dispatch_sound : PendingKeySound.Sound dispatch := by
  refine ⟨⟨by decide +kernel, ?_⟩, ?_, ?_, by unfold PendingKeySound.StackOk; decide +kernel⟩
  · intro i l marked
    have size : dispatch.pendingKeys.size = 3 := by decide +kernel
    have bound : i < 3 := by
      have := (Array.getElem?_eq_some_iff.mp marked).1
      omega
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · have impossible : dispatch.pendingKeys[0]? = some none := by decide +kernel
      rw [impossible] at marked
      cases marked
    · exact ⟨0, by decide +kernel, by decide⟩
    · exact ⟨2, by decide +kernel, by decide⟩
  · intro _
    decide +kernel
  · intro h
    have flow : dispatch.flowLevel = 0 := by decide +kernel
    omega

lemma output_mono : IndentStackMono.Mono valueOut := by
  intro i hi
  have size : valueOut.indents.size = 3 := by decide +kernel
  have bound : i + 1 < 3 := by simpa [size] using hi
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> decide +kernel +revert

-- The initialized compact context and actual colon's scanner proof compose.
-- This is a nonempty output domain: the root mark survives.
lemma actual_colon_payload :
    SlotValues valueOut q0 2 .blockOut valueB ∧
      NodeValues valueOut q0 2 valueB := by
  apply R2ColonComposition.scanValue_payload
    (initialized_slot endA (plainAKey 2 3 endA.chars))
    (by simp [innerMarks])
    (by intro x hx; simp only [R2JointSibling.innerMarks,
      show RegisterWitness.markedCols valueOut = [0] from by decide +kernel,
      List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)
    actual_scan
    dispatch_sound (by decide +kernel) output_mono (by decide +kernel)
  · exact SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero indB))
  · exact GLit.mk _ 2

-- Spend a genuine sibling before the surviving root's value in one input.
lemma actual_sibling_then_ancestor : SLYamlStream q0 ⟨[], 0⟩ := by
  have node : SBlockNode 3 .blockIn valueB endB :=
    letterNode 3 3 'b' endB.chars (by unfold isNsPlainSafe isNsChar; decide) (by decide)
  have frame := (actual_colon_payload.2 endB node).2 (by decide +kernel)
  have tail : SCompactMapTail 2 endB endD :=
    SCompactMapTail.cons 2 endB siblingQ endD endD
      (SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero siblingQ)))
      sibling_entry (SCompactMapTail.nil _ _)
  cases frame with
  | level _ _ _ _ cont =>
    have afterSibling := (cont endD tail).close
    have outer := afterSibling.at (own := 0) (by decide +kernel)
      (by decide +kernel)
    exact outer.2 endD valueE (SIndent.zero _) (GLit.mk _ 0) ⟨[], 0⟩
      (SBlockIndented.node 0 .blockOut valueE ⟨[], 0⟩
        (SBlockNode_blockIn_to_blockOut
          (letterNode 1 1 'e' [] (by unfold isNsPlainSafe isNsChar; decide) (by decide))))
      ⟨[], 0⟩ (SCompactMapTail.nil _ _)

#print axioms dispatch_sound
#print axioms actual_colon_payload
#print axioms actual_sibling_then_ancestor

end R2ColonCompositionConcrete
