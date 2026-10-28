import L4YAML.Proofs.Production.StreamAccum

open L4YAML.Proofs.IndentStackCover

namespace L4YAML.Proofs.StreamAccum

-- The strict-lower-level invariant excludes a root frame at root width.
lemma root_frame_impossible (ks : List FrameLevel)
    (h_lt : ∀ fr ∈ ks, fr.width < 0) :
    FrameLevel.map 0 ∉ ks := by
  intro hmem
  exact Nat.lt_irrefl 0 (h_lt (FrameLevel.map 0) hmem)

example (ks : List FrameLevel)
    (h_lt : ∀ fr ∈ ks, fr.width < 0) :
    FrameLevel.map 0 ∉ ks :=
  root_frame_impossible ks h_lt

#print axioms root_frame_impossible

end L4YAML.Proofs.StreamAccum
