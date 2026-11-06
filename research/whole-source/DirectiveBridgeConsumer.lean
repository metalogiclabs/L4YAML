module

import DirectiveBridge
import L4YAML.Parser.Composition
meta import L4YAML.Parser.Composition

/-!
# Consuming checks for the independent TAG source bridge

The general consumer requires actual scanner success and the exact token
contribution, not merely existence of a well-formed abstract trace. The public
parser controls below are separate executable observations; they do not turn
the body-level bridge into a full-language completeness result.
-/

namespace MathGraph.WholeSource.DirectiveBridgeConsumer

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open MathGraph.WholeSource.DirectiveBridge

lemma consumes_exact_token (sc : ScannerState) {handle tagPrefix : List Char}
    {s t : SurfPos} (h : TagDirective handle tagPrefix s t)
    (hcorr : ScannerSurfCorr sc s) (hallow : sc.allowDirectives = true) :
    ∃ out, scanDirective sc = .ok out ∧
      ScannerSurfCorr out t ∧
      out.tokens.toList = sc.tokens.toList ++
        [{ pos := sc.currentPos, val := .tagDirective (String.ofList handle) (String.ofList tagPrefix) }] ∧
      out.directivesPresent = true := by
  obtain ⟨out, hok, hsource, htoken, hflag⟩ :=
    scanDirective_accepts sc h hcorr hallow
  refine ⟨out, hok, hsource, ?_, hflag⟩
  simp [htoken]

lemma consumes_preserved_context (sc : ScannerState) {handle tagPrefix : List Char}
    {s t : SurfPos} (h : TagDirective handle tagPrefix s t)
    (hcorr : ScannerSurfCorr sc s) (hallow : sc.allowDirectives = true) :
    ∃ out, scanDirective sc = .ok out ∧ DirectiveContextKeeps sc out := by
  obtain ⟨out, hok, _, _, _⟩ := scanDirective_accepts sc h hcorr hallow
  exact ⟨out, hok, scanDirective_context sc out h hcorr hallow hok⟩

/-- A constructive arbitrary-length family on the actual original input.
No scanner success or scanner correspondence is assumed by this consumer. -/
lemma original_source_family (input : String) (handle tagPrefix rest : List Char)
    (hh : TagHandle handle)
    (hp : ∀ c ∈ tagPrefix, L4YAML.CharPredicates.isUriCharProp c)
    (hne : tagPrefix ≠ [])
    (hsource : input.toList =
      '%' :: 'T' :: 'A' :: 'G' :: ' ' :: (handle ++ ' ' :: (tagPrefix ++ '\n' :: rest))) :
    ∃ out, scanDirective (ScannerState.mk' input) = .ok out ∧
      ScannerSurfCorr out ⟨'\n' :: rest, 5 + handle.length + 1 + tagPrefix.length⟩ ∧
      out.tokens.toList =
        [{ pos := (ScannerState.mk' input).currentPos, val := .tagDirective (String.ofList handle) (String.ofList tagPrefix) }] ∧
      out.directivesPresent = true := by
  have hc := initial_corr input input.toList (chars_from_zero_toList input)
  rw [hsource] at hc
  simpa [ScannerState.mk'] using consumes_exact_token (ScannerState.mk' input)
    (tagDirective_before_lf handle tagPrefix rest hh hp hne) hc rfl

/-- The actual parser's directive consumer retains both declaration strings. -/
lemma parser_consumes_tag (handle tagPrefix : String) (pos : YamlPos) :
    (L4YAML.TokenParser.parseDirectives
      (L4YAML.TokenParser.ParseState.mk' #[{ pos := pos, val := .tagDirective handle tagPrefix }])).1 =
      #[.tag handle tagPrefix] := by
  unfold L4YAML.TokenParser.parseDirectives
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size, List.forIn_cons,
    L4YAML.TokenParser.ParseState.mk', L4YAML.TokenParser.ParseState.peek?,
    L4YAML.TokenParser.ParseState.advance, bind, pure]

/-- Source-to-parser declaration bridge for the same arbitrary original input.
This stops at `parseDirectives`; it does not claim complete-document parsing. -/
lemma original_source_declaration (input : String) (handle tagPrefix rest : List Char)
    (hh : TagHandle handle)
    (hp : ∀ c ∈ tagPrefix, L4YAML.CharPredicates.isUriCharProp c)
    (hne : tagPrefix ≠ [])
    (hsource : input.toList =
      '%' :: 'T' :: 'A' :: 'G' :: ' ' :: (handle ++ ' ' :: (tagPrefix ++ '\n' :: rest))) :
    ∃ out, scanDirective (ScannerState.mk' input) = .ok out ∧
      (L4YAML.TokenParser.parseDirectives (L4YAML.TokenParser.ParseState.mk' out.tokens)).1 =
        #[.tag (String.ofList handle) (String.ofList tagPrefix)] := by
  obtain ⟨out, hok, _, htok, _⟩ := original_source_family input handle tagPrefix rest hh hp hne hsource
  refine ⟨out, hok, ?_⟩
  have heq : out.tokens = #[{ pos := (ScannerState.mk' input).currentPos, val := .tagDirective (String.ofList handle) (String.ofList tagPrefix) }] := by
    apply Array.toList_inj.mp
    simpa using htok
  rw [heq]
  exact parser_consumes_tag _ _ _

private def accepts (input : String) : Bool :=
  (L4YAML.TokenParser.parseYaml input).toOption.isSome

-- Actual source inputs, including all three valid handle spellings.
#guard accepts "%TAG ! tag:x,2000:\n--- !a b" = true
#guard accepts "%TAG !! tag:x,2000:\n--- !!a b" = true
#guard accepts "%TAG !long-name42! tag:x,2000:\n--- !long-name42!a b" = true
#guard accepts "%TAG !t! tag:x,2000:\r\n--- !t!a b" = true
#guard accepts "%TAG !t! tag:x,2000:  \n--- !t!a b" = true
#guard accepts "%TAG !t! tag:x,2000:\n--- !t!a café" = true

-- Shape rejection must survive the stronger source interface.
#guard accepts "%TAG \n---" = false
#guard accepts "%TAG !a tag:x,2000:\n---" = false
#guard accepts "%TAG !!! tag:x,2000:\n---" = false
#guard accepts "%TAG a! tag:x,2000:\n---" = false

-- A valid local body is not sufficient for a complete document: the actual
-- consumer still requires a document-start marker and a defined tag handle.
#guard accepts "%TAG !t! tag:x,2000:\n!t!a b" = false
#guard accepts "%TAG !t! tag:x,2000:\n--- !other!a b" = false

-- Preserve the protected semantic answer, not acceptance alone. Changing
-- only the declaration changes the resolved tag of the same node spelling.
private def rootTags (input : String) : Option (Array (Option String)) :=
  (L4YAML.TokenParser.parseYaml input).toOption.map fun docs =>
    docs.map fun doc => match doc.value with
      | .scalar scalar => scalar.tag
      | .sequence _ _ tag _ => tag
      | .mapping _ _ tag _ => tag
      | .alias _ => none

#guard rootTags "%TAG !t! tag:x,2000:\n--- !t!a b" = some #[some "tag:x,2000:a"]
#guard rootTags "%TAG !t! tag:y,2000:\n--- !t!a b" = some #[some "tag:y,2000:a"]
#guard rootTags "%TAG !t! tag:x,2000:\n--- !t!a b\n...\n%TAG !t! tag:y,2000:\n--- !t!a b" =
  some #[some "tag:x,2000:a", some "tag:y,2000:a"]
#guard accepts "%TAG !t! tag:x,2000:\n--- !t!a b\n...\n--- !t!a b" = false

#print axioms consumes_exact_token
#print axioms consumes_preserved_context
#print axioms original_source_family
#print axioms parser_consumes_tag
#print axioms original_source_declaration

end MathGraph.WholeSource.DirectiveBridgeConsumer
