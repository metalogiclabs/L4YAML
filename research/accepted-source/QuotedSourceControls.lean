module

public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition
public import L4YAML.Proofs.Production.Acceptance.Quoted
public meta import L4YAML.Proofs.Production.Acceptance.Quoted

/-! Adversarial instantiation before a same-grammar quoted inverse.
Capstone path: quoted source reconstruction -> no-drop accepted source fragment
-> Blueprint group 7.7 (revised acceptance/serialization biconditional).
These are actual implementation observations, not universal proofs. -/

namespace L4YAML.Research.AcceptedSource

open L4YAML Scanner Surface

def leafAccept (input : String) : Bool :=
  (scanDoubleQuoted (ScannerState.mk' input)).toOption.isSome

def publicAccept (input : String) : Bool :=
  (TokenParser.parseYaml input).toOption.isSome

-- Constructive positive observations, including decoded controls and multibyte input.
#guard leafAccept "\"\"" = true
#guard leafAccept "\"a\"" = true
#guard leafAccept "\"é\"" = true
#guard leafAccept "\"𝄞\"" = true
#guard leafAccept "\"\\n\"" = true
#guard leafAccept "\"\\x00\"" = true
#guard leafAccept "\"\\0\"" = true
#guard leafAccept "\"\\uD7FF\"" = true
#guard leafAccept "\"\\uE000\"" = true
#guard leafAccept "\"\\U0010FFFF\"" = true

-- The old broad relation admits these; the actual scanner rejects them.
#guard leafAccept "\"\x01\"" = false
#guard leafAccept "\"\\uD800\"" = false
#guard leafAccept "\"\\uDFFF\"" = false
#guard leafAccept "\"\\U00110000\"" = false
#guard leafAccept "\"\\UFFFFFFFF\"" = false
#guard leafAccept "\"\\q\"" = false
#guard leafAccept "\"a\"b" = false
#guard leafAccept "\"" = false

-- Source-position/decoded-value observations are independent literal oracles.
def leafSnapshot (input : String) : Option (String × Nat × Nat × Nat) :=
  match scanDoubleQuoted (ScannerState.mk' input) with
  | .error _ => none
  | .ok s => match s.tokens[0]?.map (·.val) with
    | some (.scalar content .doubleQuoted) => some (content, s.offset, s.col, s.tokens.size)
    | _ => none

#guard leafSnapshot "\"\"" = some ("", 2, 2, 1)
#guard leafSnapshot "\"a\"" = some ("a", 3, 3, 1)
#guard leafSnapshot "\"é\"" = some ("é", 4, 3, 1)
#guard leafSnapshot "\"𝄞\"" = some ("𝄞", 6, 3, 1)
#guard leafSnapshot "\"\\n\"" = some ("\n", 4, 4, 1)
#guard leafSnapshot "\"\\x00\"" = some ("\x00", 6, 6, 1)

-- A leaf can succeed on a prefix: final EOF must be a distinct premise.
#guard leafSnapshot "\"a\" " = some ("a", 3, 3, 1)
#guard publicAccept "\"a\" " = true

-- Original source variants: no assumption that input equals emitter output.
#guard publicAccept "[\"a\",\"b\"]" = true
#guard publicAccept "[\"a\", \"b\"]" = true
#guard publicAccept "[\"\",\"\\n\"]" = true
#guard publicAccept "[\"é\",\"𝄞\"]" = true
#guard publicAccept "[\"a\",\"b\"" = false
#guard publicAccept "[\"a\",\"b\"}" = false
#guard publicAccept "[\"a\",,\"b\"]" = false
#guard publicAccept "[\"a\",\"b\"]junk" = false
#guard publicAccept "a" = true

-- Whole-array and last-end-marker hypotheses alone do not force parser exhaustion.
def earlyEndTokens : Array (Positioned YamlToken) :=
  #[{ pos := ⟨0, 0, 0⟩, val := .streamStart }, { pos := ⟨0, 0, 0⟩, val := .streamEnd },
    { pos := ⟨0, 0, 0⟩, val := .scalar "ignored" .doubleQuoted },
    { pos := ⟨0, 0, 0⟩, val := .streamEnd }]

#guard (TokenParser.parseStream earlyEndTokens).toOption.map Array.size = some 0

end L4YAML.Research.AcceptedSource
