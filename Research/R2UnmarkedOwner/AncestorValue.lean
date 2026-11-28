import Research.R2ConsumptionClosure.EntryValues

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.IndentStackCover (FrameLevel)

namespace R2UnmarkedOwner

-- Strengthen an existing informative value continuation. This field keeps
-- its old stream answer and also the entire smaller-column family after
-- every sibling tail of the consumed owner, whether that owner stays marked.
def AncestorValue (sc : ScannerState) (start : SurfPos) (own : Nat) (e : SurfPos) : Prop :=
  ResumeFrames (SLYamlStream start) [FrameLevel.map own] e ∧
  ∀ z, SCompactMapTail own e z → ValuesBelow sc (SLYamlStream start) own z

lemma AncestorValue.restrict_state {before after : ScannerState}
    {start e : SurfPos} {own : Nat} (h : AncestorValue before start own e)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before) :
    AncestorValue after start own e :=
  ⟨h.1, fun z tail => (h.2 z tail).narrow back⟩

lemma AncestorValue.of_entries {before after : ScannerState}
    {start e i c v : SurfPos} {own : Nat}
    (family : EntryValues before (SLYamlStream start) e)
    (marked : own ∈ RegisterWitness.markedCols before)
    (back : ∀ x ∈ RegisterWitness.markedCols after, x ∈ RegisterWitness.markedCols before)
    (indent : SIndent own e i) (literal : GLit ':' i c)
    (content : SBlockIndented own .blockOut c v) : AncestorValue after start own v := by
  have step := ValuesBelow.at family marked (marked_lt_ceiling marked)
  have retained := step.2 i c indent literal v content
  exact ⟨ResumeFrames.one (fun z tail => (retained z tail).close),
    fun z tail => (retained z tail).narrow back⟩

lemma AncestorValue.pair {sc : ScannerState} {start v : SurfPos} {own ancestor : Nat}
    (h : AncestorValue sc start own v)
    (marked : ancestor ∈ RegisterWitness.markedCols sc) (lt : ancestor < own) :
    ExplValueLine start ancestor v :=
  (h.2 v (SCompactMapTail.nil own v)).valueLine marked lt

#print axioms AncestorValue.of_entries
#print axioms AncestorValue.restrict_state
#print axioms AncestorValue.pair

end R2UnmarkedOwner
