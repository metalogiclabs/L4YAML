import Research.R2ConsumptionClosure.ConcreteSuppliers
import L4YAML.Parser.Composition

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness

namespace R2PayloadControls

def rootQuestion (input : String) : ScannerState :=
  match scanNextToken ((ScannerState.mk' input).emit .streamStart) with
  | .ok (some s) => s
  | _ => ScannerState.mk' input

lemma root_marks : markedCols (rootQuestion R2ConcreteSuppliers.input4) = [0] := by decide +kernel
example : (rootQuestion R2ConcreteSuppliers.input4).offset = 1 ∧
    (rootQuestion R2ConcreteSuppliers.input4).col = 1 := by decide +kernel

def rootValueSource : String := "? a\n: b\n? c\n: d\n"
lemma simple_question_marks : markedCols (rootQuestion rootValueSource) = [0] := by decide +kernel
lemma value_marks : markedCols (R2ConcreteSuppliers.afterFirstColon rootValueSource) = [] := by decide +kernel
example : (R2ConcreteSuppliers.afterFirstColon rootValueSource).offset = 5 ∧
    (R2ConcreteSuppliers.afterFirstColon rootValueSource).col = 1 := by decide +kernel

-- These existing ancestor-bearing states cannot be mistaken for a singleton
-- root question or an empty-domain value supplier.
example : markedCols (R2ConcreteSuppliers.afterFirstColon R2ConcreteSuppliers.input4) ≠ [] := by
  simp [R2ConcreteSuppliers.marks4]
example : ¬ (∀ x ∈ markedCols (R2ConcreteSuppliers.afterFirstColon R2ConcreteSuppliers.input6), x = 6) := by
  simp [R2ConcreteSuppliers.marks6]

#guard (L4YAML.TokenParser.parseYaml rootValueSource).isOk
#guard (L4YAML.TokenParser.parseYaml
  "? ? ? ? a\n      : b\n      ? c\n      : d\n  : e\n: f\n").isOk

end R2PayloadControls
