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

#eval parseStream #[
  {pos := default, val := YamlToken.streamStart},
  {pos := default, val := YamlToken.versionDirective 1 2},
  {pos := default, val := YamlToken.documentStart},
  {pos := default, val := YamlToken.streamEnd}]

lemma parse_literal_empty_document (p0 p1 p2 p3 : YamlPos) (major minor : Nat) :
    parseStream #[
      {pos := p0, val := .streamStart},
      {pos := p1, val := .versionDirective major minor},
      {pos := p2, val := .documentStart},
      {pos := p3, val := .streamEnd}] =
      .ok #[{value := emptyNode,
             directives := #[.yaml s!"{major}.{minor}"]}] := by
  rfl

#print axioms parse_literal_empty_document
end
end MathGraph.WholeSource.DirectiveResult
