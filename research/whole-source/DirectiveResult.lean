module
public import DirectiveParse
public meta import L4YAML.Parser.Composition

/-!
# Exact parser result for a single explicit empty directive document

This module refines the acceptance theorem with a separate, non-circular
output-specification obligation. It uses the production token parser.
-/
namespace MathGraph.WholeSource.DirectiveResult
@[expose] public section
open L4YAML L4YAML.TokenParser

lemma parse_literal_empty_document (p0 p1 p2 p3 q0 q1 q2 q3 : YamlPos)
    (major minor : Nat) :
    parseStream #[
      {pos := p0, val := .streamStart, endPos := q0},
      {pos := p1, val := .versionDirective major minor, endPos := q1},
      {pos := p2, val := .documentStart, endPos := q2},
      {pos := p3, val := .streamEnd, endPos := q3}] =
      .ok #[{value := emptyNode,
             directives := #[.yaml s!"{major}.{minor}"]}] := by
  simp [parseStream, ParseState.expect, ParseState.peek?,
    parseStreamLoop, parseDocument, prepareDocumentState, parseDirectives,
    ParseState.tryConsume, ParseState.advance, StreamState.validNextToken,
    ParseState.peekPos?, emptyNode, bind, Except.bind, pure, Except.pure,
    Std.Legacy.Range.forIn_eq_forIn_range', List.range'_succ, List.range'_zero,
    List.forIn_cons, List.forIn_nil, Id.run]

/-- Positions and token-span metadata are arbitrary; the parser output is
determined by the independently proved four-token *value* image. -/
lemma parser_result_from_four_values (ts : Array (Positioned YamlToken))
    (major minor : Nat)
    (hvals : ts.map (·.val) =
      #[.streamStart, .versionDirective major minor, .documentStart, .streamEnd]) :
    parseStream ts =
      .ok #[{value := emptyNode, directives := #[.yaml s!"{major}.{minor}"]}] := by
  have hsize : ts.size = 4 := by
    have hs := congrArg Array.size hvals
    simpa using hs
  let a := ts[0]!
  let b := ts[1]!
  let c := ts[2]!
  let d := ts[3]!
  have hrepr : ts = #[a, b, c, d] := by
    apply Array.ext
    · simp [hsize]
    · intro i hi hj
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;>
        simp [a, b, c, d, hsize]
  have hv : #[a.val, b.val, c.val, d.val] =
      #[.streamStart, .versionDirective major minor, .documentStart, .streamEnd] := by
    simpa [hrepr] using hvals
  have ha : a.val = .streamStart := by
    have hh := congrArg (fun xs : Array YamlToken => xs[0]?) hv
    simpa using hh
  have hb : b.val = .versionDirective major minor := by
    have hh := congrArg (fun xs : Array YamlToken => xs[1]?) hv
    simpa using hh
  have hc : c.val = .documentStart := by
    have hh := congrArg (fun xs : Array YamlToken => xs[2]?) hv
    simpa using hh
  have hd : d.val = .streamEnd := by
    have hh := congrArg (fun xs : Array YamlToken => xs[3]?) hv
    simpa using hh
  have ea : a = {pos := a.pos, val := .streamStart, endPos := a.endPos} := by
    cases a with
    | mk p v e =>
      subst v
      rfl
  have eb : b = {pos := b.pos, val := .versionDirective major minor, endPos := b.endPos} := by
    cases b with
    | mk p v e =>
      subst v
      rfl
  have ec : c = {pos := c.pos, val := .documentStart, endPos := c.endPos} := by
    cases c with
    | mk p v e =>
      subst v
      rfl
  have ed : d = {pos := d.pos, val := .streamEnd, endPos := d.endPos} := by
    cases d with
    | mk p v e =>
      subst v
      rfl
  rw [hrepr, ea, eb, ec, ed]
  exact parse_literal_empty_document a.pos b.pos c.pos d.pos
    a.endPos b.endPos c.endPos d.endPos major minor

/-- The actual source-level raw parser returns the uniquely specified empty
document (not just an unspecified successful array). -/
lemma original_empty_document_raw_result (input : String)
    (major minor comment : List Char)
    (hma : ∀ c ∈ major, L4YAML.Surface.isNsDecDigit c)
    (hmi : ∀ c ∈ minor, L4YAML.Surface.isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ ['\n', '-', '-', '-', '\n'])))) :
    let majorNat := (String.ofList major).toNat!
    let minorNat := (String.ofList minor).toNat!
    parseYamlRaw input =
      .ok #[{value := emptyNode, directives := #[.yaml s!"{majorNat}.{minorNat}"]}] := by
  obtain ⟨raw, filtered, _hraw, hscan, _heq, hvals⟩ :=
    MathGraph.WholeSource.DirectiveEOF.original_empty_document_scans
      input major minor comment hma hmi hneMa hneMi hcomment hsource
  have hp := parser_result_from_four_values filtered
    (String.ofList major).toNat! (String.ofList minor).toNat! hvals
  simp [parseYamlRaw, hscan, hp]

#print axioms parse_literal_empty_document
#print axioms parser_result_from_four_values
#print axioms original_empty_document_raw_result
end
end MathGraph.WholeSource.DirectiveResult
