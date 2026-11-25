module
public import Tests.Guards.Proofs.AnchoredWordParser
public import Tests.Guards.Proofs.AnchoredWordGrammar
import all L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredWordAssurance
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.AnchoredWordSource
open L4YAML.Tests.Guards.AnchoredWordExecution
set_option linter.unusedSimpArgs false

lemma anchored_word_events (k v : List Char) :
 tokenEvents (expectedTokens k v)=[.defineAnchor "a"] := by
 simp [tokenEvents,go,tokenEvent,expectedTokens,ExplicitWordExecution.tok]

/-- Blueprint 7.7 source-family assurance. Only independently defined words
    are assumed. The actual native fold, exact positioned tokens, nonempty
    events, grammar reading, raw payload, composition and EOF are proved.
    This is a fragment theorem, not the universal scan_trace capstone. -/
lemma anchored_word_assurance (k v : List Char) (hk : Word k) (hv : Word v) :
 scanFiltered (AnchoredWordSource.source k v)=.ok (expectedTokens k v) ∧
 L4YAML.TokenParser.parseYamlSingleRaw (AnchoredWordSource.source k v)=.ok (AnchoredWordParser.document k v) ∧
 L4YAML.TokenParser.parseYamlSingle (AnchoredWordSource.source k v)=.ok (AnchoredWordParser.composed k v) ∧
 tokenEvents (expectedTokens k v)=[.defineAnchor "a"] ∧
 TraceOf (AnchoredWordSource.source k v) [.defineAnchor "a"] ∧
 (∀ n, scanLoop (ExplicitWordExecution.initial k (suffix v)) (n+5)=scanLoop (scalarOut k v) n) ∧
 (scalarOut k v).offset=(AnchoredWordSource.source k v).utf8ByteSize ∧
 (scalarOut k v).definedAnchors=#["a"] ∧
 scanNextToken (scalarOut k v)=.ok none := by
 exact ⟨anchored_word_filtered k v hk hv,AnchoredWordParser.parsed_raw_source k v hk hv,
  AnchoredWordParser.parsed_source k v hk hv,anchored_word_events k v,
  AnchoredWordGrammar.anchored_word_trace k v hk hv,anchored_word_fold k v hk hv,
  (scalar_eof k v hk.2 hv.2).1,by rfl,(scalar_eof k v hk.2 hv.2).2⟩

#print axioms anchored_word_events
#print axioms anchored_word_assurance
end L4YAML.Tests.Guards.AnchoredWordAssurance
