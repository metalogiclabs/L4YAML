import L4YAML.Proofs.Production.StreamAccum

open L4YAML.Proofs.IndentStackCover

namespace L4YAML.Proofs.StreamAccum

-- The carried list names only mapping levels strictly below the park's own.
lemma own_level_absent_of_lower_bound (ks : List FrameLevel) (n : Nat)
    (h_lt : ∀ fr ∈ ks, fr.width < n) :
    FrameLevel.map n ∉ ks := by
  intro hmem
  exact Nat.lt_irrefl n (h_lt (FrameLevel.map n) hmem)

example (ks : List FrameLevel) (n : Nat)
    (h_lt : ∀ fr ∈ ks, fr.width < n) :
    FrameLevel.map n ∉ ks :=
  own_level_absent_of_lower_bound ks n h_lt

-- The strict-lower-level invariant excludes a root frame at root width.
lemma root_frame_impossible (ks : List FrameLevel)
    (h_lt : ∀ fr ∈ ks, fr.width < 0) :
    FrameLevel.map 0 ∉ ks :=
  own_level_absent_of_lower_bound ks 0 h_lt

example (ks : List FrameLevel)
    (h_lt : ∀ fr ∈ ks, fr.width < 0) :
    FrameLevel.map 0 ∉ ks :=
  root_frame_impossible ks h_lt

#print axioms own_level_absent_of_lower_bound
#print axioms root_frame_impossible

end L4YAML.Proofs.StreamAccum
