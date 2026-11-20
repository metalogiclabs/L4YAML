/-
The minimal GROUP 7.7 serialization consumer, re-targeted from global
scanner-only S3 and full trace uniqueness to the exact obligations that
the existing *parse-success* proof chain actually needs.

Exact independent source parent:
  nasa-jpl/L4YAML experiment/metagraph-problem
  aeacc60258b89fc1c5bb34b6f0ba9a5286801c02
No axioms, sorry, scanner changes, or changed formal grammar.
-/
module

public import L4YAML.Proofs.Composition
public import L4YAML.Proofs.Serialization.ScannerShape
public import L4YAML.Proofs.Serialization.TraceOf.Document

@[expose] public section Blanket

namespace L4YAML.Tests.Guards.S3ConsumerRetarget

open L4YAML
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.Composition
open L4YAML.Proofs.Serialization.ScannerShape
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

/-- Property-relative semantic confluence, deliberately WEAKER than
equality of all event lists. -/
def WFAdequacy (input : String) : Prop :=
  ∀ e₁ e₂ : List Event,
    TraceOf input e₁ → TraceOf input e₂ →
    (SerializationWellFormed e₁ ↔ SerializationWellFormed e₂)

/-- The genuinely required scanner-to-source bridge is restricted to inputs
for which the native token parser ALSO succeeds. This is a candidate
obligation, *not* here declared as a theorem about L4YAML. -/
def ParsedTraceBridge : Prop :=
  ∀ input : String, ∀ ts : Array (Positioned YamlToken),
    ∀ raw : Array YamlDocument,
    scanFiltered input = .ok ts →
    parseStream ts = .ok raw →
    TraceOf input (tokenEvents ts)

/-- A second, independent obligation: a successfully parsed input's
annotated trace interpretations all agree on the WELL-FORMEDNESS verdict,
not necessarily on their full event lists. -/
def ParsedVerdictBridge : Prop :=
  ∀ input : String, ∀ ts : Array (Positioned YamlToken),
    ∀ raw : Array YamlDocument,
    scanFiltered input = .ok ts →
    parseStream ts = .ok raw →
    WFAdequacy input

/-- This is the decisive PROOF-ARCHITECTURE experiment.
The already checked scanner/parse decomposition, S5 and checker correctness
compose with the TWO weaker candidate bridges, giving the EXACT forward
serialization conclusion wanted by the capstone.
Neither candidate bridge is assumed to have been proved by this theorem.
-/
theorem forward_wellformedness_from_two_minimal_bridges
    (hS3 : ParsedTraceBridge)
    (hVerdict : ParsedVerdictBridge)
    (input : String) (rawDocs : Array YamlDocument)
    (hParsed : parseYamlRaw input = .ok rawDocs) :
    TraceWellFormed input := by
  obtain ⟨ts, hs, hp⟩ := parseYamlRaw_ok_decompose input rawDocs hParsed
  have hTrace : TraceOf input (tokenEvents ts) :=
    hS3 input ts rawDocs hs hp
  have hCheck : checkFrom {} (tokenEvents ts) = true :=
    scanFiltered_parseStream_ok_checkFrom_full input ts rawDocs hs hp
  have hWF : SerializationWellFormed (tokenEvents ts) :=
    (serializationWellFormed_iff_check (tokenEvents ts)).2 hCheck
  have hAdeq : WFAdequacy input :=
    hVerdict input ts rawDocs hs hp
  intro ev he
  exact (hAdeq (tokenEvents ts) ev hTrace he).mp hWF

#print axioms L4YAML.Tests.Guards.S3ConsumerRetarget.forward_wellformedness_from_two_minimal_bridges

end L4YAML.Tests.Guards.S3ConsumerRetarget

end Blanket
