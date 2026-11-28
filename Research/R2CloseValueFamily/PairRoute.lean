import Research.R2UnmarkedOwner.AncestorValue

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum

namespace R2CloseValueFamily

-- The old paired ancestor obligation is a reader of the retained whole
-- value, with the consumed owner's arbitrary mapping tail still available.
lemma pairAt_of_route {sc : ScannerState} {start gram : SurfPos} {own : Nat}
    (route : ∀ m i c, SSLComments gram m → SIndent own m i → GLit ':' i c →
      ∀ v, SBlockIndented own .blockOut c v → R2UnmarkedOwner.AncestorValue sc start own v) :
    ∀ a ∈ RegisterWitness.markedCols sc, a < own →
      ∀ m i c, SSLComments gram m → SIndent own m i → GLit ':' i c →
      ∀ v, SBlockIndented own .blockOut c v → ExplValueLine start a v :=
  fun _a marked lower m i c comments indent literal v value =>
    (route m i c comments indent literal v value).pair marked lower

lemma wholePack {sc : ScannerState} {start gram : SurfPos}
    (route : ∀ own ∈ RegisterWitness.markedCols sc,
      ∀ m i c, SSLComments gram m → SIndent own m i → GLit ':' i c →
      ∀ v, SBlockIndented own .blockOut c v → R2UnmarkedOwner.AncestorValue sc start own v) :
    ∃ ns : List Nat, RegisterWitness.MarkedColsIn sc ns ∧
      (∀ own ∈ ns, ∀ m i c, SSLComments gram m → SIndent own m i → GLit ':' i c →
        ∀ v, SBlockIndented own .blockOut c v → R2UnmarkedOwner.AncestorValue sc start own v) ∧
      (∀ own ∈ ns, ∀ a ∈ RegisterWitness.markedCols sc, a < own →
        ∀ m i c, SSLComments gram m → SIndent own m i → GLit ':' i c →
        ∀ v, SBlockIndented own .blockOut c v → ExplValueLine start a v) :=
  ⟨RegisterWitness.markedCols sc, RegisterWitness.MarkedColsIn.self sc,
    route, fun own marked => pairAt_of_route (route own marked)⟩

#print axioms pairAt_of_route
#print axioms wholePack

end R2CloseValueFamily
