/-
Group 7.7 contract admission experiment, frozen library parent
14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f.

Question: does the documented forward serialization consumer require S3 on
EVERY successful scan, or only on scans whose actual token parser succeeds?

The proofs below compose the repository's actual pipeline factorization,
scanner/parser serialization theorem and token-parser completeness theorem.
They check sufficiency of explicitly stated interfaces. They do not prove
those interfaces, define ExactSurfaceLanguage, close scan_trace, or establish
Group 7.7. In particular the reverse certificate contains no parser-success
premise: its missing producer must come from independently specified source
language membership and serialization validity.

Scope: the legacy TokenParser.parseYaml API. The indexed/limited FFI entry
points and decoded scalar values are separate correspondence obligations.
-/
module

public import L4YAML.Proofs.Serialization.ExecutableBoundary
public import L4YAML.Proofs.Serialization.ScannerShape
public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Parser.StreamCompleteness

@[expose] public section Blanket

namespace L4YAML.Tests.Guards.AcceptedTraceContract

open L4YAML
open L4YAML.Proofs.Serialization
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.TokenGrammar

/-! Boundary controls, before the composition proofs.
The seven-byte case passes the old scanner and fails its real parser: the
parser-qualified contract does not owe this scan-only case. An undeclared
alias fails in the scanner itself, so a reverse source-to-scanner producer
cannot in general be justified by surface syntax alone. -/

#guard "? -\n  :".utf8ByteSize == 7
#guard "? -\n  :".toList == ['?', ' ', '-', '\n', ' ', ' ', ':']
#guard (match Scanner.scanFiltered "" with | .ok _ => true | .error _ => false)
#guard (match TokenParser.parseYaml "" with | .ok _ => true | .error _ => false)
#guard (match Scanner.scanFiltered "? -\n  :" with | .ok _ => true | .error _ => false)
#guard (match TokenParser.parseYaml "? -\n  :" with | .ok _ => false | .error _ => true)
#guard (match Scanner.scanFiltered "*x" with
  | .error (.undefinedAlias ..) => true
  | _ => false)

/-- Group 7.7's documented forward consumer only needs a trace of the
scanner output when the actual token parser succeeds on that output.
The trace contract is deliberately a visible, unpaid premise. -/
lemma accepted_trace_exists
    (input : String) (docs : Array YamlDocument)
    (hparse : TokenParser.parseYaml input = .ok docs)
    (haccepted : ∀ (ts : Array (Positioned YamlToken)) (rawDocs : Array YamlDocument),
      Scanner.scanFiltered input = .ok ts →
      TokenParser.parseStream ts = .ok rawDocs →
      TraceOf input (tokenEvents ts)) :
    ∃ ev, TraceOf input ev ∧ SerializationWellFormed ev := by
  obtain ⟨ts, rawDocs, hs, hp⟩ :=
    (parse_iff_executable_language input).mp ⟨docs, hparse⟩
  refine ⟨tokenEvents ts, haccepted ts rawDocs hs hp, ?_⟩
  exact (serializationWellFormed_iff_check (tokenEvents ts)).mpr
    (ScannerShape.scanFiltered_parseStream_ok_checkFrom_full input ts rawDocs hs hp)

/-- The same parser-qualified trace contract suffices for the real forward
serialization consequence once all grammar traces agree on serialization
validity. Full trace equality would imply this coherence premise, but is
stronger than this particular consumer needs. Neither premise is proved here. -/
lemma accepted_trace_contract_suffices_for_forward_serialization
    (input : String) (docs : Array YamlDocument)
    (hparse : TokenParser.parseYaml input = .ok docs)
    (haccepted : ∀ (ts : Array (Positioned YamlToken)) (rawDocs : Array YamlDocument),
      Scanner.scanFiltered input = .ok ts →
      TokenParser.parseStream ts = .ok rawDocs →
      TraceOf input (tokenEvents ts))
    (hcoherent : ∀ (good ev : List Event),
      TraceOf input good → TraceOf input ev →
      SerializationWellFormed good → SerializationWellFormed ev) :
    TraceWellFormed input := by
  obtain ⟨chosen, hchosen, hwell⟩ :=
    accepted_trace_exists input docs hparse haccepted
  intro ev hev
  exact hcoherent chosen ev hchosen hev hwell

/-- Group 7.7's reverse composition consumes a successful scan, its actual
token-grammar derivation, and a source-grammar trace of those same tokens.
TraceWellFormed supplies TokenStateOk, and the existing parseStream_accepts
then supplies parser success. No parser-success hypothesis is assumed.

Missing producer, not proved here: independently justified exact source
language membership together with TraceWellFormed must construct hcertificate.
A parser-qualified trace theorem cannot supply that certificate before parse
success is established; using it here would be circular. -/
lemma scanned_trace_certificate_suffices_for_reverse_acceptance
    (input : String) (hwell : TraceWellFormed input)
    (hcertificate : ∃ ts : Array (Positioned YamlToken),
      Scanner.scanFiltered input = .ok ts ∧
      TokenGrammar ts ∧ TraceOf input (tokenEvents ts)) :
    ∃ docs, TokenParser.parseYaml input = .ok docs := by
  obtain ⟨ts, hs, hgrammar, htrace⟩ := hcertificate
  have hstate : TokenStateOk ts := hwell (tokenEvents ts) htrace
  obtain ⟨rawDocs, hp⟩ := parseStream_accepts ts hgrammar hstate
  exact ⟨rawDocs.map YamlDocument.compose,
    L4YAML.Proofs.Composition.parseYaml_pipeline input ts rawDocs hs hp⟩

#print axioms accepted_trace_exists
#print axioms accepted_trace_contract_suffices_for_forward_serialization
#print axioms scanned_trace_certificate_suffices_for_reverse_acceptance

end L4YAML.Tests.Guards.AcceptedTraceContract

end Blanket
