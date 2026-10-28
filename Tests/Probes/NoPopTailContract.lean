import L4YAML.Proofs.Production.StreamAccum

namespace L4YAML.Surface

-- Candidate compact-tail composition for the capstone's mapping continuation.
lemma SCompactMapTail.append {n : Nat} {a b c : SurfPos}
    (hab : SCompactMapTail n a b)
    (hbc : SCompactMapTail n b c) :
    SCompactMapTail n a c :=
  match hab with
  | .nil _ _ => hbc
  | .cons n s s₁ s₂ _ h_indent h_entry h_tail =>
      SCompactMapTail.cons n s s₁ s₂ c h_indent h_entry
        (SCompactMapTail.append h_tail hbc)

-- A nonempty prefix may shift an *already supplied* mapping continuation.
lemma SCompactMapTail.shift {P : SurfPos → Prop} {n : Nat} {a b : SurfPos}
    (continueMap : ∀ c, SCompactMapTail n a c → P c)
    (hab : SCompactMapTail n a b) :
    ∀ c, SCompactMapTail n b c → P c :=
  fun c hbc => continueMap c (SCompactMapTail.append hab hbc)

example {n : Nat} {a b c : SurfPos}
    (hab : SCompactMapTail n a b)
    (hbc : SCompactMapTail n b c) :
    SCompactMapTail n a c :=
  SCompactMapTail.append hab hbc

example {P : SurfPos → Prop} {n : Nat} {a b : SurfPos}
    (continueMap : ∀ c, SCompactMapTail n a c → P c)
    (hab : SCompactMapTail n a b) :
    ∀ c, SCompactMapTail n b c → P c :=
  SCompactMapTail.shift continueMap hab

#print axioms SCompactMapTail.append
#print axioms SCompactMapTail.shift

end L4YAML.Surface

open L4YAML.Surface
open L4YAML.Proofs.IndentStackCover

namespace L4YAML.Proofs.StreamAccum

-- If the own mapping-level continuation is supplied, a sibling's nonempty
-- mapping tail can be consed without changing any lower resume frames.
lemma ResumeFrames.repark_map_tail {P : SurfPos → Prop} {n : Nat}
    {ks : List FrameLevel} {a b : SurfPos}
    (h_lt : ∀ fr ∈ ks, fr.width < n)
    (h_map : ∀ c, SCompactMapTail n a c → ResumeFrames P ks c)
    (hab : SCompactMapTail n a b) :
    ResumeFrames P (FrameLevel.map n :: ks) b :=
  ResumeFrames.level n ks b h_lt
    (fun c hbc => h_map c (SCompactMapTail.append hab hbc))

example {P : SurfPos → Prop} {n : Nat} {ks : List FrameLevel} {a b : SurfPos}
    (h_lt : ∀ fr ∈ ks, fr.width < n)
    (h_map : ∀ c, SCompactMapTail n a c → ResumeFrames P ks c)
    (hab : SCompactMapTail n a b) :
    ResumeFrames P (FrameLevel.map n :: ks) b :=
  ResumeFrames.repark_map_tail h_lt h_map hab

#print axioms ResumeFrames.repark_map_tail

end L4YAML.Proofs.StreamAccum
