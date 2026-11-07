module

public import QuotedPublic
public import CapstoneObstructions
public meta import Lean

/-! Group 7.7's source-side proof obligation. This is NOT a definition of valid
YAML. The language parameter must be supplied independently. The generic
composition below is conditional; only the quoted instance is discharged here.
The two negative instances prevent reusing known over-approximations as if the
interface itself repaired them. All instances reuse already checked evidence. -/

@[expose] public section
namespace MathGraph.WholeSource.SourceBridge
open L4YAML L4YAML.Proofs.TokenGrammar
open L4YAML.Research.AcceptedSource
open MathGraph.WholeSource.CapstoneObstructions

/-- Obligation to PRODUCE the actual scan and both parser premises from an
independent source judgment. No scanner-success premise is supplied. -/
def Obligation (Language : String → Prop) : Prop :=
  ∀ input, Language input →
    ∃ ts, Scanner.scanFiltered input = .ok ts ∧ TokenGrammar ts ∧ TokenStateOk ts

/-- The already-proved parser half discharges acceptance once the source
producer exists. This lemma does not construct that producer for full YAML. -/
lemma accepts_of_producer {Language : String → Prop} (producer : Obligation Language) :
    ∀ input, Language input → ∃ docs, TokenParser.parseYaml input = .ok docs := by
  intro input hs
  obtain ⟨ts, hscan, hshape, hstate⟩ := producer input hs
  obtain ⟨docs, hparse⟩ := parseStream_accepts ts hshape hstate
  exact ⟨docs.map YamlDocument.compose,
    L4YAML.Proofs.Composition.parseYaml_pipeline input ts docs hscan hparse⟩

-- Source-only restricted grammar, imported rather than reconstructed.
def QuotedSource (input : String) : Prop :=
  ∃ col, L4YAML.Proofs.Acceptance.SCDoubleQuotedOk
    ⟨input.toList, 0⟩ ⟨[], col⟩

lemma quoted_producer : Obligation QuotedSource := by
  intro input hs
  obtain ⟨ts, content, hscan, hvals⟩ := source_quoted_scan_tokens input hs
  obtain ⟨hshape, hstate⟩ := source_quoted_token_conditions ts content hvals
  exact ⟨ts, hscan, hshape, hstate⟩

/-- Known false source grammars cannot satisfy this stronger producer goal. -/
lemma original_producer_impossible : ¬ Obligation Surface.InYamlLanguage := by
  intro h
  exact original_converse_refuted (accepts_of_producer h)

lemma repaired_stream_producer_impossible : ¬ Obligation RepairedWellFormed := by
  intro h
  exact repaired_completeness_refuted (accepts_of_producer h)

#check Obligation
#check accepts_of_producer
#check quoted_producer
#check original_producer_impossible
#check repaired_stream_producer_impossible

open Lean Elab Command in
run_cmd do
  for n in [``accepts_of_producer, ``quoted_producer,
      ``original_producer_impossible, ``repaired_stream_producer_impossible] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"SOURCE_BRIDGE_AXIOMS {n}: {axs}"

end MathGraph.WholeSource.SourceBridge
