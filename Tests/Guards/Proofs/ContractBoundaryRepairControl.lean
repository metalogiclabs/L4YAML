import L4YAML.Schema.Schema
import L4YAML.Proofs.Schema.SchemaResolution
import L4YAML.Spec.CoreSchema

/-!
Matched repair-arm native checks at historical L4YAML PR #302 head.
Source: bb790c7e93f2d2f2ffa40b6178ccc3f675a94504
Repaired schema blob: bda62ed5cad86edcf2a1a40abe297053e80af226
Formal schema table blob: 94145db07d86ebd957d116b617827b00737fc9d3
Proof blob: 2153a0dd73688a794587689df8c8f5770b1a4407
External requirement: https://yaml.org/spec/1.2.2/#1032-tag-resolution

This is a positive-control branch for the existing, OPEN PR #302, not a
claim of merged upstream repair. A universal *tag* theorem does not prove
numeric value correctness, document parsing, or C/Python translation.
-/

namespace ContractBoundaryRepairControl

open L4YAML.Schema
open L4YAML.Proofs.SchemaResolution

-- The stronger source-to-contract theorem exists on this repair revision.
theorem repaired_all_tags :
    ∀ s : String, coreTagCorrespondence s :=
  coreTagCorrespondenceAll

-- Identical bad-source examples as the historical unpatched arm.
theorem correct_empty_hex_string :
    (resolveImplicit "0x").isStr = true := by decide
theorem correct_underscore_string :
    (resolveImplicit "1_000").isStr = true := by decide
theorem correct_trailing_dot_float :
    (resolveImplicit "1.").isFloat = true := by decide

-- Additional boundary spelling conditions.
theorem correct_uppercase_hex_prefix_string :
    (resolveImplicit "0XFF").isStr = true := by decide
theorem correct_signed_hex_string :
    (resolveImplicit "-0xF").isStr = true := by decide

-- Identical negative controls are preserved.
theorem correct_decimal :
    (resolveImplicit "1000").isInt = true := by decide
theorem correct_zero :
    (resolveImplicit "0").isInt = true := by decide
theorem correct_hex :
    (resolveImplicit "0xFF").isInt = true := by decide
theorem correct_octal :
    (resolveImplicit "0o17").isInt = true := by decide
theorem correct_bool :
    (resolveImplicit "true").isBool = true := by decide
theorem correct_null :
    (resolveImplicit "Null").isNull = true := by decide
theorem correct_string :
    (resolveImplicit "yes").isStr = true := by decide

#print axioms ContractBoundaryRepairControl.repaired_all_tags
#print axioms ContractBoundaryRepairControl.correct_empty_hex_string
#print axioms ContractBoundaryRepairControl.correct_underscore_string
#print axioms ContractBoundaryRepairControl.correct_trailing_dot_float

end ContractBoundaryRepairControl
