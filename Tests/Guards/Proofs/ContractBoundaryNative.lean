import L4YAML.Schema.Schema
import L4YAML.Proofs.Schema.SchemaResolution

/-!
# Contract boundary: native Lean witness, *unpatched* 2026-11-21

This experimental module imports the actual source at its pinned historical
parent, not a Python reconstruction. It adds no production code and asserts
only a finite, published-standards-backed sample set.

Repository branch parent: b9e0a5b52f8731afbe603b4ae0f32df438073319
Schema.lean blob: 5fb5bccfd3b6cccd164f68a678ef2ea812803fe0
SchemaResolution.lean blob: 603185cad7208f21fc7d6fa3d593438ce3122542
External independent specification: https://yaml.org/spec/1.2.2/#1032-tag-resolution

The source-derived *internal* proposition is `resolveImplicit_complete`.
The explicit expected samples are a human-transcribed excerpt of the published
external table, not a new general formalization of the YAML specification.
-/

namespace ContractBoundaryNative

open L4YAML.Schema
open L4YAML.Proofs.SchemaResolution

inductive Tag where
  | null | bool | int | float | str | collection
  deriving DecidableEq, Repr, BEq

def actualTag : YamlType → Tag
  | .null => .null
  | .bool _ => .bool
  | .int _ => .int
  | .float _ => .float
  | .str _ => .str
  | .seq _ => .collection
  | .map _ => .collection

/-- Selected external Core Schema §10.3.2 tag requirements, NOT an
    exhaustive classifier: exhaustive external tag correspondence remains
    outside this finite witness module's verification boundary. -/
def requiredTag : String → Tag
  | "0x" => .str
  | "0" => .int
  | "1_000" => .str
  | "1000" => .int
  | "1." => .float
  | "0xFF" => .int
  | "0o17" => .int
  | "true" => .bool
  | "Null" => .null
  | "yes" => .str
  | _ => .str

-- Preexisting internal theorem: totality is green for an offending input.
theorem internal_green_at_bad_hex :
    (resolveImplicit "0x").isNull ||
    (resolveImplicit "0x").isBool ||
    (resolveImplicit "0x").isInt ||
    (resolveImplicit "0x").isFloat ||
    (resolveImplicit "0x").isStr = true :=
  resolveImplicit_complete "0x"

-- Native, kernel-reducible counterexamples: the unpatched implementation
-- disagrees with the independent scalar-tag requirements in three mechanisms.
theorem wrong_empty_hex :
    actualTag (resolveImplicit "0x") ≠ requiredTag "0x" := by decide

theorem wrong_underscore_integer :
    actualTag (resolveImplicit "1_000") ≠ requiredTag "1_000" := by decide

theorem wrong_trailing_dot_float :
    actualTag (resolveImplicit "1.") ≠ requiredTag "1." := by decide

-- Property-relative information loss: equal actual downstream values
-- correspond to distinct normative tags, not just a string-label mismatch.
theorem empty_hex_collapses_into_zero :
    resolveImplicit "0x" = resolveImplicit "0" := by rfl

theorem underscore_collapses_into_decimal :
    resolveImplicit "1_000" = resolveImplicit "1000" := by rfl

theorem required_hex_zero_distinct :
    requiredTag "0x" ≠ requiredTag "0" := by decide

theorem required_underscore_decimal_distinct :
    requiredTag "1_000" ≠ requiredTag "1000" := by decide

-- Negative controls: a faithful checker must not flag these.
theorem correct_decimal :
    actualTag (resolveImplicit "1000") = requiredTag "1000" := by decide

theorem correct_zero :
    actualTag (resolveImplicit "0") = requiredTag "0" := by decide

theorem correct_hex :
    actualTag (resolveImplicit "0xFF") = requiredTag "0xFF" := by decide

theorem correct_octal :
    actualTag (resolveImplicit "0o17") = requiredTag "0o17" := by decide

theorem correct_bool :
    actualTag (resolveImplicit "true") = requiredTag "true" := by decide

theorem correct_null :
    actualTag (resolveImplicit "Null") = requiredTag "Null" := by decide

theorem correct_string :
    actualTag (resolveImplicit "yes") = requiredTag "yes" := by decide

#print axioms ContractBoundaryNative.internal_green_at_bad_hex
#print axioms ContractBoundaryNative.wrong_empty_hex
#print axioms ContractBoundaryNative.wrong_underscore_integer
#print axioms ContractBoundaryNative.wrong_trailing_dot_float
#print axioms ContractBoundaryNative.empty_hex_collapses_into_zero
#print axioms ContractBoundaryNative.underscore_collapses_into_decimal

end ContractBoundaryNative
