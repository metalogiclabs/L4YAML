module
public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition
public meta import Lean
set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.AcceptanceScope
open L4YAML L4YAML.TokenParser

/-- Composition adds no acceptance condition at this public API. This is an
implementation boundary, not an independent grammar definition. -/
theorem public_accepts_iff_raw (input : String) :
    (∃ docs, parseYaml input = .ok docs) ↔
      (∃ raw, parseYamlRaw input = .ok raw) := by
  cases h : parseYamlRaw input with
  | error e => simp [parseYaml, h]
  | ok raw => simp [parseYaml, h]

/-- Exact output relationship at this boundary; no claim that compose implements
all normative graph, schema, or key-equality requirements follows from this. -/
theorem public_output_iff (input : String) (docs : Array YamlDocument) :
    parseYaml input = .ok docs ↔
      ∃ raw, parseYamlRaw input = .ok raw ∧ docs = raw.map YamlDocument.compose := by
  cases h : parseYamlRaw input with
  | error e => simp [parseYaml, h]
  | ok raw => simp [parseYaml, h, eq_comm]

-- Separating controls: syntactic acceptance is not schema/content validation.
#guard (parseYaml "!!int not-an-integer").toOption.isSome = true
#guard (parseYaml "{a: 1, a: 2}").toOption.isSome = true
#guard (parseYaml "*missing").toOption.isSome = false
#guard (parseYaml "!missing!item value").toOption.isSome = false
#check public_accepts_iff_raw
#check public_output_iff
#print axioms public_accepts_iff_raw
#print axioms public_output_iff
open Lean Elab Command in
run_cmd do
  for n in [``public_accepts_iff_raw, ``public_output_iff] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"ACCEPTANCE_SCOPE_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.AcceptanceScope
