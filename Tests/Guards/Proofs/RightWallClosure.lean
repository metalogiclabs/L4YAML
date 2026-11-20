/-
MathGraph Right-Wall closure experiment
Read-only proof-adequacy controls pinned to nasa-jpl/L4YAML owner SHA
b9e0a5b52f8731afbe603b4ae0f32df438073319.
Not an upstream production change and not a proof of YAML 1.2.2 conformance.
-/
module

public import L4YAML.Spec.Grammar
public import L4YAML.Proofs.Serialization.ExecutableBoundary
public import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Parser.Composition
public import L4YAML.Schema.Schema
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Schema.Schema
public import L4YAML.Proofs.Serialization.RefLex
public meta import L4YAML.Proofs.Serialization.RefLex

@[expose] public section

namespace L4YAML.Proofs.RightWallClosure

open L4YAML.Grammar
open L4YAML.Proofs.Serialization
open L4YAML.Proofs.Serialization.TraceOf

/-!
# Probe A: the record named Grammar.ValidYaml is not tied to its source input

The construction preserves all grammar/value evidence while replacing
the source string arbitrarily. It challenges record adequacy only,
not the kernel, the code parser, or the undeclared 7.7 capstone.
-/

private def arbitraryValidYaml (source : String) : ValidYaml :=
  { input := source
    value := toYamlValue .emptyNode
    grammar := .emptyNode
    corresponds := NodeToValue.emptyNode }

lemma any_source_has_ValidYaml_record (source : String) :
    ∃ witness : ValidYaml, witness.input = source := by
  exact ⟨arbitraryValidYaml source, rfl⟩

/-- Stronger property: the *same* grammar and value evidence can be carried
    by a record whose source string is replaced arbitrarily. -/
lemma rebind_source_preserves_grammar_and_value
    (w : ValidYaml) (newSource : String) :
    ∃ rebound : ValidYaml,
      rebound.input = newSource ∧
      rebound.grammar = w.grammar ∧
      rebound.value = w.value := by
  exact ⟨{ w with input := newSource }, rfl, rfl, rfl⟩

-- Independent negative control: SOH is forbidden as a raw YAML source character.
-- The existence of this record says nothing about YAML acceptance.
example : ∃ witness : ValidYaml, witness.input = "\u0001" :=
  any_source_has_ValidYaml_record "\u0001"

-- Native parser controls: unlike the source-free record, the actual parser
-- distinguishes a valid scalar from raw U+0001 (forbidden by YAML 1.2.2 §5.1).
#guard (L4YAML.TokenParser.parseYaml "a").isOk
#guard !(L4YAML.TokenParser.parseYaml "\u0001").isOk

/-! # Probe C: independent source lexer versus native parser on [211] -/
-- Bounded source-pinned *observed divergence* (not the desired contract):
-- native parser accepts one plain scalar; the independent reference lexer
-- invents an alias on its continuation line and rejects the trace.
-- These pins document the baseline and should be REVERSED when refLex is fixed.
#guard (L4YAML.TokenParser.parseYaml "a\n*x").isOk
#guard L4YAML.Proofs.Serialization.EventsOf.eventsOf "a\n*x" =
  [.useAlias "x"]
#guard L4YAML.Proofs.Serialization.EventsOf.wellFormedB "a\n*x" = false
#guard L4YAML.Proofs.Serialization.EventsOf.wellFormedB "a" = true

#eval (L4YAML.TokenParser.parseYaml "a\n*x").isOk
#eval L4YAML.Proofs.Serialization.EventsOf.eventsOf "a\n*x"
#eval L4YAML.Proofs.Serialization.EventsOf.wellFormedB "a\n*x"
#eval L4YAML.Proofs.Serialization.EventsOf.eventsOf "a\n&x"
#eval L4YAML.Proofs.Serialization.EventsOf.wellFormedB "a\n&x"

/-! ## Probe D: acceptance proof cannot certify Core Schema semantics.
This tests the already known upstream defect addressed by open PR #302.
It is not a new reported defect or a proposed final schema specification.
YAML 1.2.2 §10.3.2 requires 1_000 and 0x to be strings, 1. to be float.
-/
#guard (L4YAML.TokenParser.parseYaml "1_000").isOk
#guard (L4YAML.TokenParser.parseYaml "0x").isOk
#guard (L4YAML.TokenParser.parseYaml "1.").isOk
#guard (L4YAML.Schema.resolveImplicit "1_000").isInt
#guard (L4YAML.Schema.resolveImplicit "0x").isInt
#guard (L4YAML.Schema.resolveImplicit "1.").isStr

/-! # Probe E: directive route choices reflect actual scanner behavior. -/
#eval (L4YAML.TokenParser.parseYaml "a\n%YAML 1.2\n---\nb").isOk
#eval (L4YAML.TokenParser.parseYaml "a\n...\n%YAML 1.2\n---\nb").isOk
#eval (L4YAML.TokenParser.parseYaml "a\n---\nb").isOk

-- Positive control: even an ordinary scalar source gets the very same empty-node witness.
example : ∃ witness : ValidYaml, witness.input = "a" :=
  any_source_has_ValidYaml_record "a"

/-!
# Probe B: the consumer-first end-to-end cut

Four externally meaningful obligations are explicit:
* forward_surface: executable acceptance implies the exact specified surface;
* forward_trace: accepted input is well-formed across ALL admissible traces;
* backward_scanner: an exact, serializable source is scanned successfully;
* backward_parser: its scanner tokens actually parse.

ExactSurface is a parameter because the project's corrected
ExactSurfaceLanguage has not yet been declared. This assembly theorem
DOES NOT discharge any of the four obligations.
-/

lemma acceptance_iff_from_four_bridges
    (ExactSurface : String → Prop)
    (forward_surface : ∀ s, InExecutableLanguage s → ExactSurface s)
    (forward_trace : ∀ s, InExecutableLanguage s → TraceWellFormed s)
    (backward_scanner :
      ∀ s, ExactSurface s → TraceWellFormed s →
        ∃ ts, L4YAML.Scanner.scanFiltered s = .ok ts)
    (backward_parser :
      ∀ s ts, ExactSurface s → TraceWellFormed s →
        L4YAML.Scanner.scanFiltered s = .ok ts →
        ∃ rawDocs, L4YAML.TokenParser.parseStream ts = .ok rawDocs)
    (source : String) :
    (∃ docs, L4YAML.TokenParser.parseYaml source = .ok docs) ↔
      (ExactSurface source ∧ TraceWellFormed source) := by
  rw [parse_iff_executable_language]
  constructor
  · intro h
    exact ⟨forward_surface source h, forward_trace source h⟩
  · rintro ⟨hSurface, hTrace⟩
    obtain ⟨ts, hScan⟩ := backward_scanner source hSurface hTrace
    obtain ⟨rawDocs, hParse⟩ :=
      backward_parser source ts hSurface hTrace hScan
    exact ⟨ts, rawDocs, hScan, hParse⟩

#print axioms any_source_has_ValidYaml_record
#print axioms rebind_source_preserves_grammar_and_value
#print axioms acceptance_iff_from_four_bridges

/-!
# Proof-route test: exactly why S3 is useful and exactly why S3 alone cannot finish 7.7.

A scanner trace (S3) plus scanner-token serialization well-formedness (S5)
only establishes the *universal* target when a uniqueness proof (S4)
identifies every grammatical trace with the scanner's trace.
The current grammar refutes S4 on some block/document inputs.
-/
lemma scanner_trace_closes_universal_if_unique
    (source : String)
    (tokens : Array (L4YAML.Positioned L4YAML.YamlToken))
    (hS3 : TraceOf source (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents tokens))
    (hS4 : ∀ e₁ e₂, TraceOf source e₁ → TraceOf source e₂ → e₁ = e₂)
    (hS5 : L4YAML.Proofs.Serialization.SerializationWellFormed.SerializationWellFormed
      (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents tokens)) :
    TraceWellFormed source := by
  intro ev hTrace
  rw [hS4 ev (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents tokens) hTrace hS3]
  exact hS5

#print axioms scanner_trace_closes_universal_if_unique

end L4YAML.Proofs.RightWallClosure
