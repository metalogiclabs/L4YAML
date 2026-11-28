import Research.R2ConsumptionClosure.EntryValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)

namespace L4YAML.Proofs.R2InvariantPayload

-- The existing informative payload gains a context, not a fresh alternative.
-- A value's consumed mapping stays open for siblings. A question still owns
-- its mark and retains that mapping tail inside EntryValues' own EntryStep.
def NodeValues (sc : ScannerState) (start : SurfPos) (own : Nat) (slot : SurfPos) : Prop :=
  ∀ e, SBlockNode (own + 1) .blockIn slot e →
    EntryValues sc (SLYamlStream start) e ∧
    (own ∉ RegisterWitness.markedCols sc →
      KeyFrames (EntryValues sc (SLYamlStream start)) [FrameLevel.map own] e)

lemma EntryValues.of_no_marks {sc : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (empty : RegisterWitness.markedCols sc = []) (h : P e) : EntryValues sc P e := by
  simpa [EntryValues, columnCeiling, ValuesBelow, empty] using h

lemma ValuesBelow.of_no_lower_marks {sc : ScannerState} {P : SurfPos → Prop}
    {upper : Nat} {e : SurfPos} (none : ∀ x < upper, x ∉ RegisterWitness.markedCols sc)
    (h : P e) : ValuesBelow sc P upper e := by
  induction upper with
  | zero => exact h
  | succ n ih =>
    have hm := none n (by omega)
    simp only [ValuesBelow, if_neg hm]
    exact ih (fun x hx => none x (by omega))

lemma ValuesBelow.of_only_owner {sc : ScannerState} {P : SurfPos → Prop}
    {upper own : Nat} {e : SurfPos}
    (only : ∀ x ∈ RegisterWitness.markedCols sc, x = own)
    (step : EntryStep P own e) : ValuesBelow sc P upper e := by
  induction upper generalizing e with
  | zero => exact step.1 e (SCompactMapTail.nil own e)
  | succ n ih =>
    by_cases hm : n ∈ RegisterWitness.markedCols sc
    · have eq := only n hm
      subst n
      simp only [ValuesBelow, if_pos hm]
      exact step.map (fun z hz => ValuesBelow.of_no_lower_marks
        (fun x hx hmem => by have := only x hmem; omega) hz)
    · simpa only [ValuesBelow, if_neg hm] using ih step

lemma NodeValues.of_question {sc : ScannerState} {start q slot : SurfPos} {own : Nat}
    (literal : GLit '?' q slot)
    (route : ∀ v, SBlockMapEntry own q v →
      ∀ z, SCompactMapTail own v z → SLYamlStream start z)
    (only : ∀ x ∈ RegisterWitness.markedCols sc, x = own) :
    NodeValues sc start own slot := by
  intro e node
  have step := entryStep_of_question literal route
    (SBlockIndented.node own .blockOut slot e (SBlockNode_blockIn_to_blockOut node))
  constructor
  · exact ValuesBelow.of_only_owner only step
  · intro noOwn
    have empty : RegisterWitness.markedCols sc = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      exact noOwn ((only x hx) ▸ hx)
    exact KeyFrames.mapLevel own [] e (by simp) (fun z tail =>
      KeyFrames.bottom z (EntryValues.of_no_marks empty (step.1 z tail)))

lemma NodeValues.of_no_marks {sc : ScannerState} {start slot : SurfPos} {own : Nat}
    (empty : RegisterWitness.markedCols sc = [])
    (route : ∀ e, SBlockNode (own + 1) .blockIn slot e →
      ∀ z, SCompactMapTail own e z → SLYamlStream start z) :
    NodeValues sc start own slot := by
  intro e node
  constructor
  · exact EntryValues.of_no_marks empty (route e node e (SCompactMapTail.nil own e))
  · intro _
    exact KeyFrames.mapLevel own [] e (by simp) (fun z tail =>
      KeyFrames.bottom z (EntryValues.of_no_marks empty (route e node z tail)))

-- Spend the stored mapping tail before projecting an ancestor's value line.
-- This lets existing frame consumers use the new payload without closing
-- the consumed mapping prematurely or discarding its possible siblings.
lemma NodeValues.framed_ancestor {sc : ScannerState} {start slot e : SurfPos}
    {own ancestor : Nat} (payload : NodeValues sc start own slot)
    (consumed : own ∉ RegisterWitness.markedCols sc)
    (marked : ancestor ∈ RegisterWitness.markedCols sc)
    (node : SBlockNode (own + 1) .blockIn slot e) :
    KeyFrames (ExplValueLine start ancestor) [FrameLevel.map own] e := by
  have frame := (payload e node).2 consumed
  cases frame with
  | level _ _ _ _ cont =>
    exact KeyFrames.mapLevel own [] e (by simp) (fun z tail =>
      KeyFrames.bottom z (ValuesBelow.valueLine (cont z tail).close marked
        (marked_lt_ceiling marked)))

lemma own_frame_cover {sc : ScannerState} {own : Nat}
    (mono : IndentStackMono.Mono sc) (top : sc.currentIndent ≤ (own : Int)) :
    IndentStackCover.Floor own (own + 1) [FrameLevel.map own] ∧
      IndentStackCover.Covered own [FrameLevel.map own] sc := by
  constructor
  · refine ⟨Nat.le_succ own, ?_⟩
    intro e he
    have eq := List.eq_of_mem_singleton he
    rw [eq]
    exact Nat.le_refl own
  · intro e he kind floor
    have le := mono.le_currentIndent e he
    have eq : e.column = (own : Int) := by omega
    simp [eq]

#print axioms NodeValues.of_question
#print axioms NodeValues.of_no_marks
#print axioms NodeValues.framed_ancestor
#print axioms own_frame_cover

end L4YAML.Proofs.R2InvariantPayload
