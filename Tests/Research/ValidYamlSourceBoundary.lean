import L4YAML.Spec.Grammar

namespace L4YAML.Grammar

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

end L4YAML.Grammar
