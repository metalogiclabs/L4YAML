import L4YAML.Parser.Composition
import L4YAML.Proofs.Serialization.TraceOf.Document

namespace L4YAML.Tests.Guards.BareRouteLanding
open Scanner

private def landing (input : String) (priorSteps : Nat) :
    Option (Nat × Nat × Char × List Int × Bool) := do
  let mut s := (ScannerState.mk' input).emit .streamStart
  for _ in [:priorSteps] do
    let some t ← (scanNextToken s).toOption | none
    s := t
  let some (p, c) ← (scanNextToken_preprocess s).toOption | none
  let some t ← (scanNextToken s).toOption | none
  return (p.line, p.col, c, p.indents.toList.map (·.column), (danglingNodePos? t).isNone)

private def values (s : String) : Option (Array YamlValue) :=
  (TokenParser.parseYaml s).toOption.map (fun ds => ds.map (·.value))

private def plain (s : String) : YamlValue := .scalar {content := s, style := .plain}

#guard values "a\n*x" == some #[plain "a *x"]
#guard values "a\n--- b" == some #[plain "a", plain "b"]

-- After the anchor, deeper content fills its enclosing mapping value.
#guard landing "k:\n  a: &p\n    b" 5 == some (2, 4, 'b', [-1, 0, 2], true)
#guard values "k:\n  a: &p\n    b" == some #[
    .mapping .block #[(plain "k", .mapping .block #[(plain "a", plain "b")] none none)] none none]

-- At the enclosing mapping's own indentation the candidate key remains dangling.
#guard landing "k:\n  a: &p\n  c: d" 5 == some (2, 2, 'c', [-1, 0, 2], false)

open Surface Proofs.Serialization.TraceOf

-- Neither grammar can spend the explicit-document premise at the landed b.
theorem landedSourceHasNoMarker (stop : SurfPos) :
    ¬ SLExplicitDocument ⟨['b'], 4⟩ stop := by
  intro h
  cases h with
  | withContent _ _ marker _ => cases marker

theorem landedTraceHasNoMarker (stop : SurfPos) (events) :
    ¬ TLExplicitDocument ⟨['b'], 4⟩ stop events := by
  intro h
  cases h with
  | withContent _ _ _ _ marker _ => cases marker

end L4YAML.Tests.Guards.BareRouteLanding
