module
public import QuotedContinuation
import all L4YAML.Proofs.Serialization.TokenEvents
public meta import Lean
@[expose] public section
namespace MathGraph.WholeSource.TagQuotedParse
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.TokenGrammar
open L4YAML.Proofs.Serialization.SerializationWellFormed
open MathGraph.WholeSource.DirectiveBridge
open MathGraph.WholeSource.QuotedContinuation

private lemma events_ignore_positions (xs : List (Positioned YamlToken))
    (pending : List String) :
    L4YAML.Proofs.Serialization.TokenEvents.go xs pending =
      L4YAML.Proofs.Serialization.TokenEvents.go
        (xs.map (fun x => ({pos := default, val := x.val} : Positioned YamlToken))) pending := by
  induction xs generalizing pending with
  | nil => rfl
  | cons t tail ih =>
    cases h : t.val <;>
      simp [L4YAML.Proofs.Serialization.TokenEvents.go,
        L4YAML.Proofs.Serialization.TokenEvents.tokenEvent, h, ih]

/-- Independent token syntax and serialization validity from the exact value
image. No parser acceptance is used to establish these premises. -/
lemma tag_quoted_token_conditions (ts : Array (Positioned YamlToken))
    (handle pfx value : String)
    (hv : ts.map (·.val) = #[.streamStart, .tagDirective handle pfx,
      .documentStart, .scalar value .doubleQuoted, .streamEnd]) :
    TokenGrammar ts ∧ TokenStateOk ts := by
  have hat (i : Nat) : tok ts i =
      (#[.streamStart, .tagDirective handle pfx, .documentStart,
        .scalar value .doubleQuoted, .streamEnd] : Array YamlToken)[i]? := by
    simp [tok, ← hv]
  have h0 : tok ts 0 = some .streamStart := by simpa using hat 0
  have h1 : tok ts 1 = some (.tagDirective handle pfx) := by simpa using hat 1
  have h2 : tok ts 2 = some .documentStart := by simpa using hat 2
  have h3 : tok ts 3 = some (.scalar value .doubleQuoted) := by simpa using hat 3
  have h4 : tok ts 4 = some .streamEnd := by simpa using hat 4
  have hsize : ts.size = 5 := by
    have heq := congrArg Array.size hv
    simpa using heq
  constructor
  · have hdir : TG ts .directives 1 2 := by
      apply TG.directives_cons
      · simp [isDirective, h1]
      · apply TG.directives_nil
        simp [isDirective, h2]
    have hnode : TG ts .node 3 4 := by
      refine TG.node (m := 3) (TG.props_none ?_) ?_ (TG.content_scalar h3)
      · simp [isProp, h3]
      · intro hlt; omega
    have hdoc : TG ts .document 1 4 := by
      apply TG.document (d := 2) (e := 3)
      · exact hdir
      · left
        refine ⟨h2, rfl, ?_⟩
        simp [DocStartLineOk, isBlockStart, h3]
      · exact hnode
    refine ⟨h0, 4, ?_, by omega⟩
    exact TG.stream_doc h1 (by simp) (by simp) rfl hdoc (by omega)
      (by simp [h4]) (TG.stream_end (Or.inl h4))
  · have he : L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts =
        L4YAML.Proofs.Serialization.TokenEvents.go
          ((ts.map (·.val)).toList.map
            (fun v => ({pos := default, val := v} : Positioned YamlToken))) [] := by
      simpa [L4YAML.Proofs.Serialization.TokenEvents.tokenEvents,
        Array.toList_map, List.map_map, Function.comp_def] using events_ignore_positions ts.toList []
    unfold TokenStateOk
    rw [he, hv]
    by_cases hn : L4YAML.Proofs.Serialization.TokenEvents.isNamedHandle handle = true <;>
      simp [L4YAML.Proofs.Serialization.TokenEvents.go,
        L4YAML.Proofs.Serialization.TokenEvents.tokenEvent, hn,
        SerializationWellFormed, WellFormedFrom]

lemma tag_quoted_public_accepts (input : String) (handle pfx body : List Char)
    (col endCol : Nat)
    (htag : TagDirective handle pfx ⟨input.toList, 0⟩
      ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: body, col⟩)
    (hbody : SCDoubleQuotedOk ⟨body, 0⟩ ⟨[], endCol⟩) :
    ∃ docs, L4YAML.TokenParser.parseYaml input = .ok docs := by
  obtain ⟨ts, value, hscan, hvals⟩ := tag_quoted_scans input handle pfx body col endCol htag hbody
  obtain ⟨hgrammar, hstate⟩ := tag_quoted_token_conditions ts
    (String.ofList handle) (String.ofList pfx) value hvals
  obtain ⟨docs, hparse⟩ := parseStream_accepts ts hgrammar hstate
  refine ⟨docs.map YamlDocument.compose, ?_⟩
  simp [L4YAML.TokenParser.parseYaml, L4YAML.TokenParser.parseYamlRaw, hscan, hparse]

#guard (L4YAML.TokenParser.parseYaml "%TAG ! x\n---\n\"café\"").toOption.isSome = true
#guard (L4YAML.TokenParser.parseYaml "%TAG !e! tag:example.org,2000:\n---\n\"\\u0001\"").toOption.isSome = true
#guard (L4YAML.TokenParser.parseYaml "%TAG ! x\n---x\n\"a\"").toOption.isSome = false
#guard (L4YAML.TokenParser.parseYaml "%TAG ! x\n---\n\"\u0001\"").toOption.isSome = false
#check tag_quoted_public_accepts
open Lean Elab Command in
run_cmd do
  for n in [``tag_quoted_token_conditions, ``tag_quoted_public_accepts] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"TAG_QUOTED_PARSE_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.TagQuotedParse
