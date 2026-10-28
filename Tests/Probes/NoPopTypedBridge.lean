import L4YAML.Proofs.Production.StreamAccum

/-!
# No-pop route: source-native direct-application boundary

`h_closeF_old` at both builders is a sequence-tail continuation.  The
`indicator_open_map` target needs a mapping-tail continuation.  Test the
direct application using the actual L4YAML grammar and ResumeFrames types.

This does not exclude derivations using other scanner invariants or a newly
supplied mapping continuation.  It is not a counterexample to a YAML theorem.
-/

open L4YAML.Surface
open L4YAML.Proofs.IndentStackCover

namespace L4YAML.Proofs.StreamAccum

example {n : Nat} {sp_start sp_mid : SurfPos} {ks : List FrameLevel}
    (_closeSeq : ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end)
    (closeMap : ∀ sp_end, SCompactMapTail n sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    ∀ sp_end, SCompactMapTail n sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end := by
  intro sp_end h_map
  fail_if_success exact _closeSeq sp_end h_map
  exact closeMap sp_end h_map

end L4YAML.Proofs.StreamAccum
