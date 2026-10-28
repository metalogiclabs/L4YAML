import Init

/-!
A two-point abstract contract model. This is not a claim about concrete YAML
source positions or parser reachability; it tests whether a sequence-tail
closure generically implies a mapping-tail continuation.
-/
namespace L4YAML.Tests.Probes.NoPopInterfaceModel

def SeqTail (a b : Fin 2) : Prop := a = b
def MapTail (a b : Fin 2) : Prop := a = 0 ∧ b = 1
def Complete (a : Fin 2) : Prop := a = 0

theorem sequence_closure : ∀ b, SeqTail 0 b → Complete b := by
  intro b h
  exact h.symm

theorem mapping_closure_refuted : ¬ (∀ b, MapTail 0 b → Complete b) := by
  intro h
  have h1 : Complete 1 := h 1 ⟨rfl, rfl⟩
  exact (by decide : (1 : Fin 2) ≠ 0) h1

theorem sequence_does_not_imply_mapping :
    ¬ ((∀ b, SeqTail 0 b → Complete b) →
       (∀ b, MapTail 0 b → Complete b)) := by
  intro h
  exact mapping_closure_refuted (h sequence_closure)

#print axioms sequence_does_not_imply_mapping

end L4YAML.Tests.Probes.NoPopInterfaceModel
