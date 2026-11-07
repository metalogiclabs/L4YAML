module
public import DirectiveEOF
public import L4YAML.Proofs.Parser.StreamCompleteness
public meta import L4YAML.Parser.Composition

/-!
# Independent source → token grammar → actual parser, empty document family

The token-image argument uses the independently specified four-token stream,
the public `TokenGrammar` relation, and the serialization-state checker. It
does not use successful parsing to establish either parser premise.
-/
namespace MathGraph.WholeSource.DirectiveParse
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.CharPredicates
open L4YAML.Proofs.TokenGrammar
open L4YAML.Proofs.Serialization.SerializationWellFormed
open MathGraph.WholeSource.DirectiveEOF

private lemma tok_eq_get_values (ts : Array (Positioned YamlToken)) (i : Nat) :
    tok ts i = (ts.map (·.val))[i]? := by
  simp [tok]

/-- Serialization events are invariant under the source-position metadata of
tokens. This is a structural fact about the independent event extractor. -/
private lemma events_ignore_positions (xs : List (Positioned YamlToken))
    (pending : List String) :
    L4YAML.Proofs.Serialization.TokenEvents.go xs pending =
      L4YAML.Proofs.Serialization.TokenEvents.go
        (xs.map (fun x => ({pos := default, val := x.val} : Positioned YamlToken)))
        pending := by
  induction xs generalizing pending with
  | nil => rfl
  | cons t tail ih =>
    cases h : t.val <;>
      simp [L4YAML.Proofs.Serialization.TokenEvents.go,
        L4YAML.Proofs.Serialization.TokenEvents.tokenEvent, h, ih]

/-- The exact value image of the scanner's output satisfies the independent
four-token grammar and state requirements, for *all* positions and version
integers. This upgrades scanner acceptance into native parser acceptance. -/
lemma four_token_parser_accepts (ts : Array (Positioned YamlToken))
    (major minor : Nat)
    (hvals : ts.map (·.val) =
      #[.streamStart, .versionDirective major minor, .documentStart, .streamEnd]) :
    ∃ docs, L4YAML.TokenParser.parseStream ts = .ok docs := by
  have hat (i : Nat) : tok ts i =
      (#[.streamStart, .versionDirective major minor, .documentStart,
        .streamEnd] : Array YamlToken)[i]? := by
    rw [tok_eq_get_values, hvals]
  have h0 : tok ts 0 = some .streamStart := by simpa using hat 0
  have h1 : tok ts 1 = some (.versionDirective major minor) := by simpa using hat 1
  have h2 : tok ts 2 = some .documentStart := by simpa using hat 2
  have h3 : tok ts 3 = some .streamEnd := by simpa using hat 3
  have hsize : ts.size = 4 := by
    have heq := congrArg Array.size hvals
    simpa using heq
  have hdir : TG ts .directives 1 2 := by
    apply TG.directives_cons
    · simp [isDirective, h1]
    · apply TG.directives_nil
      simp [isDirective, h2]
  have hnode : TG ts .node 3 3 := by
    apply TG.node
    · apply TG.props_none
      simp [isProp, h3]
    · simp [PropsLineOk]
    · apply TG.content_empty
      simp [emptyFollower, h3]
  have hdoc : TG ts .document 1 3 := by
    apply TG.document (d := 2) (e := 3)
    · exact hdir
    · left
      refine ⟨h2, rfl, ?_⟩
      simp [DocStartLineOk, isBlockStart, h3]
    · exact hnode
  have hgram : TokenGrammar ts := by
    refine ⟨h0, 3, ?_, by omega⟩
    apply TG.stream_doc (m := 3) (t := .versionDirective major minor)
    · exact h1
    · decide
    · decide
    · decide
    · exact hdoc
    · decide
    · simp [h3]
    · exact TG.stream_end (Or.inl h3)
  have htrace : L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts =
      [.beginDocument] := by
    calc
      L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts =
          L4YAML.Proofs.Serialization.TokenEvents.go
            ((ts.map (·.val)).toList.map
              (fun v => ({pos := default, val := v} : Positioned YamlToken))) [] := by
                simpa [L4YAML.Proofs.Serialization.TokenEvents.tokenEvents,
                  Array.toList_map, List.map_map] using
                  events_ignore_positions ts.toList []
      _ = [.beginDocument] := by rw [hvals]; rfl
  have hstate : TokenStateOk ts := by
    apply (serializationWellFormed_iff_check _).2
    rw [htrace]
    rfl
  exact parseStream_accepts ts hgram hstate

/-- Source-native end-to-end theorem for independently spelled `%YAML`
comments and an explicit empty document. Uses the real scanner, parser and
composition implementations, and the original scanner fuel. -/
lemma original_empty_document_parses (input : String)
    (major minor comment : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c)
    (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ ['\n', '-', '-', '-', '\n'])))) :
    ∃ docs, L4YAML.TokenParser.parseYaml input = .ok docs := by
  obtain ⟨raw, filtered, _hraw, hscan, _heq, hvals⟩ :=
    original_empty_document_scans input major minor comment
      hma hmi hneMa hneMi hcomment hsource
  obtain ⟨docs, hparse⟩ := four_token_parser_accepts filtered
    (String.ofList major).toNat! (String.ofList minor).toNat! hvals
  refine ⟨docs.map YamlDocument.compose, ?_⟩
  simp [L4YAML.TokenParser.parseYaml, L4YAML.TokenParser.parseYamlRaw,
    hscan, hparse]

#print axioms four_token_parser_accepts
#print axioms original_empty_document_parses
end
end MathGraph.WholeSource.DirectiveParse
