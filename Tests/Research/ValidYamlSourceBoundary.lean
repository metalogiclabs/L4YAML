import L4YAML.Spec.Grammar

namespace L4YAML.Grammar

/-! A source-binding countermodel for the current ValidYaml structure.
    This is NOT a parser rejection/acceptance test or a proof of YAML 1.2.2 conformance. -/

def arbitraryInputValidYaml (s : String) : ValidYaml :=
  { input := s
    value := .scalar ⟨"", .plain, none, none, none⟩
    grammar := .emptyNode
    corresponds := NodeToValue.emptyNode }

lemma arbitraryInputValidYaml_input (s : String) :
    (arbitraryInputValidYaml s).input = s := rfl

lemma arbitraryInputValidYaml_same_value (s t : String) :
    (arbitraryInputValidYaml s).value = (arbitraryInputValidYaml t).value := rfl

lemma distinct_inputs_same_witness_payload :
    (arbitraryInputValidYaml "a").input ≠
      (arbitraryInputValidYaml "b").input ∧
    (arbitraryInputValidYaml "a").grammar =
      (arbitraryInputValidYaml "b").grammar ∧
    (arbitraryInputValidYaml "a").value =
      (arbitraryInputValidYaml "b").value := by
  constructor
  · decide
  constructor <;> rfl

/-- No function of the grammar witness alone can recover the input field
    for every inhabitant of the present ValidYaml structure. -/
lemma no_universal_source_recovery :
    ¬ ∃ (source : ValidNode → String),
      ∀ s : String, source (arbitraryInputValidYaml s).grammar =
        (arbitraryInputValidYaml s).input := by
  intro ⟨source, h⟩
  have ha : source ValidNode.emptyNode = "a" := by
    simpa [arbitraryInputValidYaml] using h "a"
  have hb : source ValidNode.emptyNode = "b" := by
    simpa [arbitraryInputValidYaml] using h "b"
  have hab : ("a" : String) = "b" := ha.symm.trans hb
  exact (by decide : ("a" : String) ≠ "b") hab

end L4YAML.Grammar
