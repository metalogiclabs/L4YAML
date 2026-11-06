module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition

/-! Intentionally false old-language acceptance expectations.
The qualification gate requires exactly these two native_decide failures,
not missing imports, malformed syntax, or other elaboration errors. -/

open L4YAML Scanner

example : (scanDoubleQuoted (ScannerState.mk' "\"\x01\"")).toOption.isSome = true := by
  native_decide

example : (scanDoubleQuoted (ScannerState.mk' "\"\\uD800\"")).toOption.isSome = true := by
  native_decide
