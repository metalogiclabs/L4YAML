import L4YAML.Proofs.Production.StreamAccum

/-!
Probe the unconditional node continuation held by a pending mapping value.
The objective is a compact mapping-tail continuation without a completed
scalar tail or a separate optional resume-frame premise.
-/

open L4YAML.Surface
open L4YAML.Proofs.IndentStackCover (FrameLevel)

namespace L4YAML.Proofs.StreamAccum

/-- The mandatory node continuation on a mapping-value park consumes any
    compact mapping tail at or below the awaited value's indentation.
    This does not use an optional frame carrier or `CompletedTail`. -/
private lemma ownerNodeCompactTail {P : SurfPos → Prop} {n k : Nat}
    {s mid : SurfPos}
    (h_le : n + 1 ≤ k)
    (h_ssl : SSLComments s mid)
    (h_node : ∀ endPos, SBlockNode (n + 1) .blockIn s endPos → P endPos) :
    ∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < k) ∧
      ∀ endPos : SurfPos, SCompactMapTail k mid endPos → ResumeFrames P ks endPos := by
  refine ⟨[], by simp, ?_⟩
  intro endPos h_tail
  apply ResumeFrames.bottom
  cases h_tail with
  | nil _ _ =>
      exact h_node _ (SBlockNode.emptyNode (n + 1) .blockIn s mid h_ssl)
  | cons _ _ _ _ _ h_ind h_entry h_tail =>
      exact h_node _ (nestedBlockMap h_le h_ssl
        (L4YAML.Proofs.NodeProduction.SBlockMapEntries_of_compactTail
          h_ind h_entry h_tail))

/-- The last real token `:` witnesses an open mapping value, not a completed
    scalar, regardless of any reservation placeholders after it. -/
private lemma completedTail_excludes_value {sc : L4YAML.Scanner.ScannerState}
    (h_last : L4YAML.Scanner.lastRealTokenVal? sc.tokens = some .value) :
    ¬ CompletedTail sc := by
  intro h_comp
  rcases h_comp with ⟨_, t, ht, hcomp⟩
  have h_eq : t = .value := Option.some.inj (ht.symm.trans h_last)
  subst t
  simp [L4YAML.YamlToken.completesFlowValue] at hcomp

#print axioms ownerNodeCompactTail
#print axioms completedTail_excludes_value

example {P : SurfPos → Prop} {n k : Nat} {s mid : SurfPos}
    (h_le : n + 1 ≤ k)
    (h_ssl : SSLComments s mid)
    (h_node : ∀ endPos, SBlockNode (n + 1) .blockIn s endPos → P endPos) :
    ∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < k) ∧
      ∀ endPos : SurfPos, SCompactMapTail k mid endPos → ResumeFrames P ks endPos :=
  ownerNodeCompactTail h_le h_ssl h_node

-- A mapping-value indicator does not complete the node it opens.  This
-- separates the owner-node path from a would-be mandatory `CompletedTail`.
example {sc : L4YAML.Scanner.ScannerState}
    (h_last : L4YAML.Scanner.lastRealTokenVal? sc.tokens = some .value) :
    ¬ CompletedTail sc :=
  completedTail_excludes_value h_last

end L4YAML.Proofs.StreamAccum
