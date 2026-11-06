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
open MathGraph.WholeSource.DirectiveBridge

lemma consumes_exact_token (sc : ScannerState) {handle prefix : List Char}
    {s t : SurfPos} (h : TagDirective handle prefix s t)
    (hcorr : ScannerSurfCorr sc s) (hallow : sc.allowDirectives = true) :
    ∃ out, scanDirective sc = .ok out ∧
      ScannerSurfCorr out t ∧
      out.tokens.toList = sc.tokens.toList ++
        [{ pos := sc.currentPos,
           val := .tagDirective (String.ofList handle) (String.ofList prefix) }] ∧
      out.directivesPresent = true := by
  obtain ⟨out, hok, hsource, htoken, hflag⟩ :=
    scanDirective_accepts sc h hcorr hallow
  refine ⟨out, hok, hsource, ?_, hflag⟩
  simp [htoken]

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

#print axioms consumes_exact_token

end MathGraph.WholeSource.DirectiveBridgeConsumer
