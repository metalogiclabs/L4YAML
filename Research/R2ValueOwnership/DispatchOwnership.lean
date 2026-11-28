import Research.R2ValueOwnership.Ownership
import L4YAML.Proofs.Production.StreamAccum

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PendingKeySound

namespace R2ValueOwnership

lemma after_colon {sc prep out : ScannerState}
    (sound : Sound sc) (mono : IndentStackMono.Mono sc)
    (preprocess : scanNextToken_preprocess sc = .ok (some (prep, ':')))
    (noflow : prep.inFlow = false)
    (dispatch : scanNextToken_dispatchBlockIndicators
      (if prep.allowDirectives then
        { prep with allowDirectives := false, documentEverStarted := true }
       else prep) ':' = .ok (some out)) : TopUnmarked out := by
  have soundPrep := PendingKeySound.preprocess_sound preprocess sound mono
  have soundDispatch : Sound (if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true }
      else prep) := by
    split
    · exact soundPrep.of_eq rfl rfl rfl rfl rfl rfl
    · exact soundPrep
  exact scanValue_top_unmarked (dispatchBlock_colon_scanValue dispatch) soundDispatch
    (by split <;> exact noflow)

#print axioms after_colon

end R2ValueOwnership
