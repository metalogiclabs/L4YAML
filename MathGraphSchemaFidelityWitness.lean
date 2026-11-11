import L4YAML.Schema.Api

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

-- The public typed Lean parser composes the unchanged scanner/parser and resolver.
-- Each statement qualifies this exact API path, not Python's separate coercer.
-- Match only the expected constructor to avoid broad equality/float assumptions.
example : (match L4YAML.parseTyped "42" with
  | .ok (.int n) => n == 42
  | _ => false) = true := by native_decide

example : (match L4YAML.parseTyped "\"42\"" with
  | .ok (.str s) => s == "42"
  | _ => false) = true := by native_decide

example : (match L4YAML.parseTyped "0x3A" with
  | .ok (.int n) => n == 58
  | _ => false) = true := by native_decide

-- Contract-disagreeing observations, if the full entry point admits the sources.
example : (match L4YAML.parseTyped "1_000" with
  | .ok (.int n) => n == 1000
  | _ => false) = true := by native_decide

example : (match L4YAML.parseTyped "0x" with
  | .ok (.int n) => n == 0
  | _ => false) = true := by native_decide

example : (match L4YAML.parseTyped "1." with
  | .ok (.str s) => s == "1."
  | _ => false) = true := by native_decide

-- Evaluated values are diagnostic only; checked propositions are above.
#eval isInt "1_000"
#eval isInt "0x"
#eval isFloat "1."
#eval L4YAML.parseTyped "1_000"
#eval L4YAML.parseTyped "0x"
#eval L4YAML.parseTyped "1."
