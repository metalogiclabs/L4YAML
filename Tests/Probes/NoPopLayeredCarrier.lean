import L4YAML.Proofs.Production.StreamAccum

/-!
Reconstruct the mapping-level continuation from a completed sequence's
own-level `ResumeFrames` result.  This is a candidate handoff contract,
not a proof that existing pending-node constructors already carry it.
-/

open L4YAML.Surface
open L4YAML.Proofs.IndentStackCover

namespace L4YAML.Proofs.StreamAccum

/-- A sequence whose completed tail returns to a still-open mapping level
    can hand the mapping tail on to the outer frame stack.  Unlike a generic
    sequence closure, the premise retains that mapping level explicitly. -/
lemma map_after_sequence_level {P : SurfPos → Prop} {n k : Nat}
    {ks : List FrameLevel} {a : SurfPos}
    (completeSeq : ∀ b, SCompactSeqTail n a b →
      ResumeFrames P (FrameLevel.map k :: ks) b) :
    ∀ b, SCompactSeqTail n a b →
      ∀ c, SCompactMapTail k b c → ResumeFrames P ks c := by
  intro b hseq c hmap
  cases completeSeq b hseq with
  | level _ _ _ _ h_cont => exact h_cont c hmap

/-- The non-popping indicator's exact optional resume witness.  The empty
    sequence tail exposes the enclosing mapping at the same landing position;
    the mapping tail may then grow by any grammar-valid continuation. -/
lemma no_pop_map_land_from_sequence {P : SurfPos → Prop} {n k : Nat}
    {ks : List FrameLevel} {a : SurfPos}
    (h_lt : ∀ fr ∈ ks, fr.width < k)
    (completeSeq : ∀ b, SCompactSeqTail n a b →
      ResumeFrames P (FrameLevel.map k :: ks) b) :
    (∃ ks' : List FrameLevel, (∀ fr ∈ ks', fr.width < k) ∧
      ∀ c, SCompactMapTail k a c → ResumeFrames P ks' c) ∨ True := by
  exact Or.inl ⟨ks, h_lt,
    map_after_sequence_level completeSeq a (SCompactSeqTail.nil n a)⟩

/-- The concrete `pendingMapValue` handoff: a completed nested block sequence
    is a block node at the mapping value's level.  The original map-value
    closure retains its own map frame, so its sequence successor can resume
    a mapping tail at that enclosing level.  This does not manufacture a
    new map frame for an unrelated landing width. -/
lemma map_land_from_nested_sequence {P : SurfPos → Prop}
    {nv k : Nat} {ks : List FrameLevel} {s s₂ s_ind s_dash : SurfPos}
    (h_le : nv + 1 ≤ k)
    (h_lt : ∀ fr ∈ ks, fr.width < nv)
    (h_ssl : SSLComments s s₂)
    (h_indent : SIndent k s₂ s_ind)
    (h_dash : GLit '-' s_ind s_dash)
    (h_gnot : GNot SNsChar s_dash)
    (closeNode : ∀ b, SBlockNode (nv + 1) .blockIn s b →
      ResumeFrames P (FrameLevel.map nv :: ks) b) :
    ∀ b, SBlockIndented k .blockIn s_dash b →
      (∃ ks' : List FrameLevel, (∀ fr ∈ ks', fr.width < nv) ∧
        ∀ c, SCompactMapTail nv b c → ResumeFrames P ks' c) ∨ True := by
  intro b h_body
  apply no_pop_map_land_from_sequence h_lt
  intro c h_seq
  exact closeNode c (nestedBlockSeq h_le h_ssl
    (L4YAML.Proofs.NodeProduction.SBlockSeqEntries_of_compactTail
      h_indent h_dash h_gnot h_body h_seq))

example {P : SurfPos → Prop} {n k : Nat} {ks : List FrameLevel} {a : SurfPos}
    (completeSeq : ∀ b, SCompactSeqTail n a b →
      ResumeFrames P (FrameLevel.map k :: ks) b) :
    ∀ b, SCompactSeqTail n a b →
      ∀ c, SCompactMapTail k b c → ResumeFrames P ks c :=
  map_after_sequence_level completeSeq

-- This is the precise optional context accepted by `indicator_open_map`:
-- it starts at the landing, before any nonempty mapping tail is consumed.
example {P : SurfPos → Prop} {n k : Nat} {ks : List FrameLevel} {a : SurfPos}
    (h_lt : ∀ fr ∈ ks, fr.width < k)
    (completeSeq : ∀ b, SCompactSeqTail n a b →
      ResumeFrames P (FrameLevel.map k :: ks) b) :
    (∃ ks' : List FrameLevel, (∀ fr ∈ ks', fr.width < k) ∧
      ∀ c, SCompactMapTail k a c → ResumeFrames P ks' c) ∨ True :=
  no_pop_map_land_from_sequence h_lt completeSeq

-- A producer of `pendingMapValue` already owns the enclosing map frame:
-- completing a nested `-` sequence yields a concrete map-tail continuation.
example {P : SurfPos → Prop} {nv k : Nat} {ks : List FrameLevel}
    {s s₂ s_ind s_dash : SurfPos}
    (h_le : nv + 1 ≤ k)
    (h_lt : ∀ fr ∈ ks, fr.width < nv)
    (h_ssl : SSLComments s s₂)
    (h_indent : SIndent k s₂ s_ind)
    (h_dash : GLit '-' s_ind s_dash)
    (h_gnot : GNot SNsChar s_dash)
    (closeNode : ∀ b, SBlockNode (nv + 1) .blockIn s b →
      ResumeFrames P (FrameLevel.map nv :: ks) b) :
    ∀ b, SBlockIndented k .blockIn s_dash b →
      (∃ ks' : List FrameLevel, (∀ fr ∈ ks', fr.width < nv) ∧
        ∀ c, SCompactMapTail nv b c → ResumeFrames P ks' c) ∨ True :=
  map_land_from_nested_sequence h_le h_lt h_ssl h_indent h_dash h_gnot closeNode

#print axioms map_after_sequence_level
#print axioms no_pop_map_land_from_sequence
#print axioms map_land_from_nested_sequence

end L4YAML.Proofs.StreamAccum
