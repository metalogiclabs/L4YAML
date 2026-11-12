module

public import L4YAML.Schema.Api
public meta import L4YAML.Schema.Api

@[expose] public section Blanket

/-!
Regression for YAML 1.2.2 Core scientific-notation zero valuation.
`0eN` denotes zero for any decimal exponent N. The public typed API must
not turn that exact, representable value into IEEE-754 NaN when `10^N`
overflows the runtime floating-point format.

The tests exercise the actual parser and schema resolver, not a shadow
arithmetic model. They make no claim about representability of nonzero
finite YAML values beyond the runtime `Float` range.
-/

open L4YAML

private def publicFiniteZero : Except ScanError Schema.YamlType → Bool
  | .ok (.float (.finite f)) => f == 0.0 && !f.isNaN && !f.isInf
  | _ => false

private def publicNegativeZero : Except ScanError Schema.YamlType → Bool
  | .ok (.float (.finite f)) => f == 0.0 && (1.0 / f).isInf && (1.0 / f) < 0.0
  | _ => false

private def publicFinite150 : Except ScanError Schema.YamlType → Bool
  | .ok (.float (.finite f)) => f == 150.0 && !f.isNaN
  | _ => false

private def publicString (s : String) : Except ScanError Schema.YamlType → Bool
  | .ok (.str actual) => actual == s
  | _ => false

private def doesNotClaimZero : Except ScanError Schema.YamlType → Bool
  | .ok (.float (.finite f)) => f != 0.0
  | _ => false

-- This is mathematically 0.1: parsing its 321-digit fractional mantissa
-- through a Float first can underflow to 0 before the 10^320 scaling.
private def tinyNonzeroMantissa : String :=
  "0." ++ String.ofList (List.replicate 320 '0') ++ "1e320"

private def parsedFiniteZero : Option Float → Bool
  | some f => f == 0.0 && !f.isNaN && !f.isInf
  | none => false

-- This class of inputs distinguishes exact zero from 0 * infinity = NaN.
#guard publicFiniteZero (parseTyped "0e309")
#guard publicFiniteZero (parseTyped "0e999")
#guard publicFiniteZero (parseTyped "0.0e999")
#guard publicFiniteZero (parseTyped "+0E309")
#guard publicNegativeZero (parseTyped "-0e999")

-- A zero guard keyed to the *rounded Float mantissa* would incorrectly
-- change this distinguishable nonzero source into zero. Its accurate
-- value remains a separate, unresolved representability issue.
#guard doesNotClaimZero (parseTyped tinyNonzeroMantissa)

-- Controls that must not change when the zero-mantissa case is repaired.
#guard publicFiniteZero (parseTyped "0e308")
#guard publicFiniteZero (parseTyped "0e-999")
#guard publicFinite150 (parseTyped "1.5e2")
#guard publicString "0e309" (parseTyped "\"0e309\"")
#guard Schema.parseFloat? "0e+" == none

-- Bounded regression sweep against the real production parser, not the
-- research-only shadow. This does not prove behavior for all exponents.
#guard (List.range 1001).all fun n =>
  parsedFiniteZero (Schema.parseFloat? ("0e" ++ toString n))
#guard (List.range 1001).all fun n =>
  parsedFiniteZero (Schema.parseFloat? ("-0e" ++ toString n))

end Blanket
