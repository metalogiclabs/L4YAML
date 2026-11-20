/-
Capstone 7.7 admission probe: YAML 1.2.2 section 6.8.2 requires each
TAG handle to be declared at most once per document, even for equal prefixes.
This test uses the actual unchanged upstream parser and token event extractor.
It is separate from the Row 19 document-continuation grammar correction.
-/
module
public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Serialization.SerializationWellFormed
public import Tests.Guards.Proofs.TagDirectiveAnnotated
import all Init.Data.Range.Basic
import all L4YAML.Proofs.Serialization.TokenEvents

@[expose] public section
namespace L4YAML.Tests.Guards.TagDirectiveContract
open L4YAML
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

def single : String := "%TAG ! !x\n--- a"
def duplicate : String := "%TAG ! !x\n%TAG ! !x\n--- a"

def scanEvents (s : String) : Option (List Event) :=
  match Scanner.scanFiltered s with
  | .ok ts => some (tokenEvents ts)
  | .error _ => none

/-- The directive lists returned by the actual parser, retaining multiplicity.
This observation is deliberately separate from the lossy event projection. -/
def parsedHandles (s : String) : Option (List (List String)) :=
  match TokenParser.parseYaml s with
  | .ok docs => some (docs.toList.map fun d => d.directives.toList.filterMap fun
      | .tag h _ => some h
      | .yaml _ => none)
  | .error _ => none

/-- YAML section 6.8.2's per-document condition on the retained handle lists.
It counts primary, secondary and named handles; prefixes do not affect it. -/
def UniqueHandlesPerDocument (hs : List (List String)) : Prop :=
  ∀ doc ∈ hs, doc.Nodup

def duplicateNamed : String := "%TAG !h! !x\n%TAG !h! !x\n--- a"
def distinctHandles : String := "%TAG !h! !x\n%TAG !g! !x\n--- a"
def separateDocuments : String := "%TAG !h! !x\n--- a\n...\n%TAG !h! !x\n--- b"
def duplicateYaml : String := "%YAML 1.2\n%YAML 1.2\n--- a"

-- Adversarial observations precede claims. Empty, legal single declaration,
-- same-handle duplicates, differing handles, document scope, YAML control.
#eval (["", single, duplicate,
  "%TAG !! !x\n%TAG !! !x\n--- a",
  "%TAG !h! !x\n%TAG !h! !x\n--- a",
  "%TAG !h! !x\n%TAG !h! !y\n--- a",
  "%TAG !h! !x\n%TAG !g! !x\n--- a",
  "%TAG !h! !x\n--- a\n...\n%TAG !h! !x\n--- b",
  "%YAML 1.2\n%YAML 1.2\n--- a"] : List String).map fun s =>
    (s, (TokenParser.parseYaml s).isOk, scanEvents s, parsedHandles s)

#guard single.toList = ['%', 'T', 'A', 'G', ' ', '!', ' ', '!', 'x', '\n', '-', '-', '-', ' ', 'a']
#guard (TokenParser.parseYaml single).isOk
#guard (TokenParser.parseYaml duplicate).isOk
#guard scanEvents single == some [.beginDocument]
#guard scanEvents duplicate == scanEvents single
#guard (TokenParser.parseYaml duplicateNamed).isOk
#guard (TokenParser.parseYaml distinctHandles).isOk
#guard (TokenParser.parseYaml separateDocuments).isOk
#guard !(TokenParser.parseYaml duplicateYaml).isOk
#guard parsedHandles single == some [["!"]]
#guard parsedHandles duplicate == some [["!", "!"]]

lemma single_parser_accepts_bit : (TokenParser.parseYaml single).isOk = true := by cbv
lemma duplicate_parser_accepts_bit : (TokenParser.parseYaml duplicate).isOk = true := by cbv
lemma same_actual_trace : scanEvents duplicate = scanEvents single := by cbv
lemma single_actual_trace : scanEvents single = some [.beginDocument] := by cbv
lemma actual_trace_well_formed : SerializationWellFormed [.beginDocument] := by
  simp [SerializationWellFormed, WellFormedFrom]

lemma single_retains_one_handle : parsedHandles single = some [["!"]] := by cbv
lemma duplicate_retains_two_handles : parsedHandles duplicate = some [["!", "!"]] := by cbv

lemma single_satisfies_requirement : UniqueHandlesPerDocument [["!"]] := by
  simp [UniqueHandlesPerDocument]

lemma duplicate_violates_requirement : ¬ UniqueHandlesPerDocument [["!", "!"]] := by
  simp [UniqueHandlesPerDocument]

/-- Actual parser success does not guarantee the section 6.8.2 requirement
on the directive handles the parser itself retains. -/
lemma parser_directive_requirement_refuted :
    ¬ (∀ s hs, parsedHandles s = some hs → UniqueHandlesPerDocument hs) := by
  intro h
  exact duplicate_violates_requirement
    (h duplicate [["!", "!"]] duplicate_retains_two_handles)

lemma single_grammar_trace :
    L4YAML.Proofs.Serialization.TraceOf.TraceOf single [.beginDocument] :=
  TagDirectiveAnnotated.single_trace

lemma duplicate_grammar_trace :
    L4YAML.Proofs.Serialization.TraceOf.TraceOf duplicate [.beginDocument] :=
  TagDirectiveAnnotated.duplicate_trace

lemma duplicate_actual_trace : scanEvents duplicate = some [.beginDocument] := by
  rw [same_actual_trace, single_actual_trace]

/-- The actual event projection cannot recover the requirement on both
concrete inputs. This does not forbid using retained tokens/source or adding
a separately proved check to ExactSurfaceLanguage. -/
lemma no_event_only_requirement_checker :
    ¬ ∃ decideRequirement : Option (List Event) → Bool,
      decideRequirement (scanEvents single) = true ∧
      decideRequirement (scanEvents duplicate) = false := by
  intro ⟨f, hs, hd⟩
  rw [same_actual_trace, hs] at hd
  cases hd

#print axioms single_parser_accepts_bit
#print axioms duplicate_parser_accepts_bit
#print axioms same_actual_trace
#print axioms single_actual_trace
#print axioms actual_trace_well_formed
#print axioms single_retains_one_handle
#print axioms duplicate_retains_two_handles
#print axioms single_satisfies_requirement
#print axioms duplicate_violates_requirement
#print axioms parser_directive_requirement_refuted
#print axioms single_grammar_trace
#print axioms duplicate_grammar_trace
#print axioms duplicate_actual_trace
#print axioms no_event_only_requirement_checker
end L4YAML.Tests.Guards.TagDirectiveContract
end
