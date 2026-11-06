module
public import DirectiveComments
public import L4YAML.Proofs.Production.Acceptance.Plain
public import L4YAML.Proofs.Scanner.ScannerCorrectness
public meta import L4YAML.Parser.Composition

/-!
# Directive-to-document structural boundary

Capstone path: original directive source → newline → document-start structural
arm → whole-stream composition → Group 7.7. This does not bypass or establish
scanNextToken's preprocessing and intervening checks.
-/
namespace MathGraph.WholeSource.DirectiveBoundary
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open MathGraph.WholeSource.DirectiveBridge
open MathGraph.WholeSource.DirectiveComments

private def accepts (s : String) : Bool := (L4YAML.TokenParser.parseYaml s).toOption.isSome
#guard accepts "%YAML 1.2 #x\n---\nvalue" = true
#guard accepts "%YAML 1.2 #x\nvalue" = false
#guard accepts "%YAML 1.2 #x\n---x" = false
#guard accepts "%YAML 1.2 #x\n ---\nvalue" = false
#guard accepts "%YAML 1.2 #x\n---\n...\n%YAML 1.2\n---\nvalue" = true
-- Same source/position, different flow context: only one structural arm accepts.
#guard (scanNextToken_dispatchStructural (ScannerState.mk' "---\n") '-').toOption.isSome = true
#guard (scanNextToken_dispatchStructural { ScannerState.mk' "---\n" with flowLevel := 1 } '-').toOption.isSome = false

/-- Correspondence alone cannot select the document-start structural arm. -/
lemma flow_context_separates_marker :
    (scanNextToken_dispatchStructural (ScannerState.mk' "---\n") '-').toOption.isSome = true ∧
    (scanNextToken_dispatchStructural { ScannerState.mk' "---\n" with flowLevel := 1 } '-').toOption.isSome = false := by
  decide

/-- The separating states agree on the current source, token array and directive
flags. The lost flow distinction alone changes structural acceptance. -/
lemma source_summary_collision :
    let base := ScannerState.mk' "---\n"
    let flow := { base with flowLevel := 1 }
    ScannerSurfCorr base ⟨"---\n".toList, 0⟩ ∧
    ScannerSurfCorr flow ⟨"---\n".toList, 0⟩ ∧
    base.tokens = flow.tokens ∧ base.directivesPresent = flow.directivesPresent ∧
    base.seenYamlDirective = flow.seenYamlDirective ∧
    (scanNextToken_dispatchStructural base '-').toOption.isSome = true ∧
    (scanNextToken_dispatchStructural flow '-').toOption.isSome = false := by
  have hc := initial_corr "---\n" "---\n".toList (chars_from_zero_toList "---\n")
  refine ⟨hc, ?_, rfl, rfl, rfl, flow_context_separates_marker⟩
  exact ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩

/-- Independent marker spelling supplies the actual lookahead predicate. -/
lemma document_start_of_source (sc : ScannerState) (rest : List Char)
    (hc : ScannerSurfCorr sc ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩) :
    atDocumentStart sc = true := by
  have hcol : sc.col = 0 := hc.col_eq.symm
  unfold atDocumentStart
  rw [hcol, peekAt_of_corr hc 0, peekAt_of_corr hc 1,
    peekAt_of_corr hc 2, peekAt_of_corr hc 3]
  rfl

lemma structural_document_start (sc : ScannerState) (rest : List Char)
    (hc : ScannerSurfCorr sc ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩)
    (hf : sc.flowLevel = 0) :
    scanNextToken_dispatchStructural sc '-' = .ok (some (scanDocumentStart sc)) := by
  have hcol : sc.col = 0 := hc.col_eq.symm
  have hflow : sc.inFlow = false := by simp [ScannerState.inFlow, hf]
  have hdoc := document_start_of_source sc rest hc
  simp [scanNextToken_dispatchStructural, hflow, hcol, hdoc]
  rfl

/-- Reuse the existing newline and flow-preservation proofs to discharge the
structural consumer's premises. No full scanNextToken success is assumed. -/
lemma directive_lf_to_document (origin out : ScannerState) (rest : List Char) (col : Nat)
    (hok : scanDirective origin = .ok out)
    (hc : ScannerSurfCorr out ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: rest, col⟩)
    (hf : origin.flowLevel = 0) :
    ScannerSurfCorr (consumeNewline out) ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ ∧
    (consumeNewline out).tokens = out.tokens ∧
    scanNextToken_dispatchStructural (consumeNewline out) '-' =
      .ok (some (scanDocumentStart (consumeNewline out))) ∧
    (scanDocumentStart (consumeNewline out)).directivesPresent = false ∧
    (scanDocumentStart (consumeNewline out)).allowDirectives = false ∧
    (scanDocumentStart (consumeNewline out)).seenYamlDirective = false := by
  obtain ⟨hn, hk⟩ := consumeNewline_accepts out (.lf _ col) hc
  have hflow : (consumeNewline out).flowLevel = 0 := by
    rw [L4YAML.Proofs.ScannerCorrectness.consumeNewline_preserves_flowLevel,
      L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_flowLevel origin out hok, hf]
  refine ⟨hn, hk.1, structural_document_start _ _ hn hflow, ?_, ?_, ?_⟩ <;>
    simp [scanDocumentStart]

/-- The original source derives every premise of the newline/structural bridge.
The source suffix after the marker remains unparsed. -/
lemma original_comment_document_boundary (input : String) (major minor comment rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ '\n' :: '-' :: '-' :: '-' :: '\n' :: rest)))) :
    ∃ out, scanDirective (ScannerState.mk' input) = .ok out ∧
      ScannerSurfCorr (consumeNewline out) ⟨'-' :: '-' :: '-' :: '\n' :: rest, 0⟩ ∧
      scanNextToken_dispatchStructural (consumeNewline out) '-' =
        .ok (some (scanDocumentStart (consumeNewline out))) ∧
      (scanDocumentStart (consumeNewline out)).directivesPresent = false ∧
      (scanDocumentStart (consumeNewline out)).allowDirectives = false ∧
      (scanDocumentStart (consumeNewline out)).seenYamlDirective = false := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  rw [hsource] at hc
  obtain ⟨out, hok, hland, _, _, _⟩ := yaml_comment_dispatch (ScannerState.mk' input)
    major minor comment ('-' :: '-' :: '-' :: '\n' :: rest)
    hma hmi hneMa hneMi hcomment hc rfl rfl
  obtain ⟨hn, _, hstruct, hd, ha, hs⟩ := directive_lf_to_document
    (ScannerState.mk' input) out rest _ hok hland rfl
  exact ⟨out, hok, hn, hstruct, hd, ha, hs⟩

#print axioms source_summary_collision
#print axioms flow_context_separates_marker
#print axioms document_start_of_source
#print axioms structural_document_start
#print axioms directive_lf_to_document
#print axioms original_comment_document_boundary
end
end MathGraph.WholeSource.DirectiveBoundary
