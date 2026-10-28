import L4YAML.Surface.Node

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
