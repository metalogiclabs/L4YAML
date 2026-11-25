module
public import Tests.Guards.Proofs.AnchoredAliasParser
public import Tests.Guards.Proofs.AnchoredAliasGrammar
import all L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredAliasAssurance
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.AnchoredWordSource (suffix)
open L4YAML.Tests.Guards.AnchoredAliasSource
open L4YAML.Tests.Guards.AnchoredAliasStates
open L4YAML.Tests.Guards.AnchoredAliasExecution
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

lemma alias_word_events (k v : List Char) :
 tokenEvents (expectedTokens k v)=[.defineAnchor "a",.useAlias "a"] := by
 simp [tokenEvents,go,tokenEvent,expectedTokens,ExplicitWordExecution.tok]

-- The dispatch's registry requirement is independently consequential for every
-- scanner state, including the actually reached alias state in this family.
lemma alias_empty_registry_rejected (s : ScannerState) :
 (scanNextToken_dispatchContent {s with definedAnchors:=#[]} '*').isOk=false := by
 simp only [scanNextToken_dispatchContent]
 simp only [show ('*'=='&')=false from by decide,show ('*'=='*')=true from by decide,
  Bool.false_eq_true,ite_false,ite_true]
 by_cases hg : (lastTokenIsNodeProperty {s with definedAnchors:=#[]} ||
    !propertyFollowerOk (anchorNameEnd {s with definedAnchors:=#[]}))=true
 · rw [if_pos hg]
   rfl
 · rw [if_neg hg]
   have hempty (n : String) : ((#[] : Array String).any (fun x => x==n))=false := by simp
   simp only [hempty,Bool.not_false,ite_true]
   rfl

/-- Blueprint 7.7: source-defined, unbounded two-entry anchor/alias assurance.
    No supplied scanner success, registry, parse result, grammar or EOF premise.
    Raw mappings are the owner's ordered YamlValue pairs, including k="copy";
    no normative key-uniqueness, schema or foreign-binding claim is made. -/
lemma alias_word_assurance (k v : List Char) (hk : Word k) (hv : Word v) :
 scanFiltered (AnchoredAliasSource.source k v)=.ok (expectedTokens k v) ∧
 L4YAML.TokenParser.parseYamlSingleRaw (AnchoredAliasSource.source k v)=.ok (AnchoredAliasParser.document k v) ∧
 L4YAML.TokenParser.parseYamlSingle (AnchoredAliasSource.source k v)=.ok (AnchoredAliasParser.composed k v) ∧
 tokenEvents (expectedTokens k v)=[.defineAnchor "a",.useAlias "a"] ∧
 TraceOf (AnchoredAliasSource.source k v) [.defineAnchor "a",.useAlias "a"] ∧
 SerializationWellFormed [.defineAnchor "a",.useAlias "a"] ∧
 (∀ n, scanLoop (ExplicitWordExecution.initial k (suffix (body v))) (n+9)=scanLoop (ao k v) n) ∧
 (ap k v).definedAnchors=#["a"] ∧ (ao k v).definedAnchors=#["a"] ∧
 (ao k v).offset=(AnchoredAliasSource.source k v).utf8ByteSize ∧
 scanNextToken (ao k v)=.ok none ∧
 (scanNextToken_dispatchContent {ap k v with definedAnchors:=#[]} '*').isOk=false := by
 exact ⟨alias_word_filtered k v hk hv,AnchoredAliasParser.parsed_raw_source k v hk hv,
  AnchoredAliasParser.parsed_source k v hk hv,alias_word_events k v,
  AnchoredAliasGrammar.alias_word_trace k v hk hv,AnchoredAliasGrammar.alias_events_wellformed,
  alias_word_fold k v hk hv,by rfl,by rfl,(ao_eof k v hk.2 hv.2).1,
  next_eof k v hk.2 hv.2,alias_empty_registry_rejected (ap k v)⟩

#print axioms alias_empty_registry_rejected
#print axioms alias_word_assurance
end L4YAML.Tests.Guards.AnchoredAliasAssurance
