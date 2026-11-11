import L4YAML.Schema.Schema

/-!
MathGraph bounded schema adequacy witness against unchanged L4YAML source.
These are positive Lean proofs of the existing implementation's decisions.
They do NOT establish conformity to YAML 1.2.2; several decisions conflict
with §10.3.2's Core Schema regexes.
-/

open L4YAML.Schema

-- Protected positive controls: accepted decimal, hexadecimal, and octal.
example : isInt "42" = some 42 := by native_decide
example : isInt "0x3A" = some 58 := by native_decide
example : isInt "0o7" = some 7 := by native_decide

-- Invalid Core Schema numeric forms are nonetheless recognized as integers.
example : isInt "1_000" = some 1000 := by native_decide
example : resolveImplicit "1_000" = .int 1000 := by rfl
example : isInt "0_1" = some 1 := by native_decide
example : isInt "0x" = some 0 := by native_decide
example : resolveImplicit "0x" = .int 0 := by rfl
example : isInt "0o" = some 0 := by native_decide

-- Valid Core Schema float spelling is left as a string on this schema path.
example : isFloat "1." = none := by rfl
example : resolveImplicit "1." = .str "1." := by rfl

-- This is a consistency witness, NOT a correctness-of-standard proof.
#eval isInt "1_000"
#eval isInt "0x"
#eval isFloat "1."
