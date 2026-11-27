import L4YAML.Proofs.Production.StreamAccum

/- Bounded producer experiment: preserve the two explicit value lines in order.
   No scanner, production proof, or capstone changes. -/
set_option autoImplicit false

namespace L4YAML.Proofs.StreamAccum
open L4YAML.Surface L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)

/-- Unlike ExplValueLine, the first value does not close the stream.
    Its continuation is the still-owed outer value line. -/
def PairedExplicitValueLine (start : SurfPos) (own outer : Nat) (atKeyEnd : SurfPos) : Prop :=
  ∀ i c : SurfPos, SIndent own atKeyEnd i → GLit ':' i c →
    ∀ v : SurfPos, SBlockIndented own .blockOut c v →
      ExplValueLine start outer v

/-- Actual question-entry chain shape from explEntryChain_of_keyContent.
    Use explicit, not explicitEmpty, before spending the ancestor. -/
theorem pair_at_question
    {start q keyStart : SurfPos} {own outer : Nat}
    (hq : GLit '?' q keyStart)
    (up : ∀ v : SurfPos, SBlockMapEntry own q v → ExplValueLine start outer v) :
    ∀ keyEnd : SurfPos, SBlockIndented own .blockOut keyStart keyEnd →
      PairedExplicitValueLine start own outer keyEnd := by
  intro keyEnd hk i c hi hc v hv
  exact up v (SBlockMapEntry.explicit own q keyStart keyEnd i c v hq hk hi hc hv)

/-- Same key construction as the landed sequence-slot producer in
    accum_block_on_closeThenBlock, now retaining the paired continuation. -/
theorem pair_at_landed_sequence
    {start q keyStart land dash entry : SurfPos} {own outer n : Nat}
    (hq : GLit '?' q keyStart)
    (up : ∀ v : SurfPos, SBlockMapEntry own q v → ExplValueLine start outer v)
    (hwidth : own ≤ n) (hssl : SSLComments keyStart land)
    (hind : SIndent n land dash) (hdash : GLit '-' dash entry)
    (hnot : GNot SNsChar entry) :
    ∀ m : SurfPos, SBlockIndented n .blockIn entry m →
      ∀ e : SurfPos, SCompactSeqTail n m e →
        PairedExplicitValueLine start own outer e := by
  intro m hm e ht
  exact pair_at_question hq up e
    (slotLandedSeq hwidth hssl
      (SBlockSeqEntries_of_compactTail hind hdash hnot hm ht))

/-- The pendingBlock -> pendingBlockContent projection preserves the pair
    when it supplies the completed sequence node from the comment suffix.
    The actual producer's existing node reconstruction supplies finish. -/
theorem pair_at_pending_content
    {start entry gram : SurfPos} {own outer n : Nat}
    (seqPair : ∀ m : SurfPos, SBlockIndented n .blockIn entry m →
      ∀ e : SurfPos, SCompactSeqTail n m e →
        PairedExplicitValueLine start own outer e)
    (finish : ∀ m : SurfPos, SSLComments gram m → SBlockIndented n .blockIn entry m) :
    ∀ m : SurfPos, SSLComments gram m →
      ∀ e : SurfPos, SCompactSeqTail n m e →
        PairedExplicitValueLine start own outer e := by
  intro m hm e ht
  exact seqPair m (finish m hm) e ht

/-- The exact shape of the priced pendingBlockContent ancestor goal,
    conditional on retaining the paired supplier and the landing's colon.
    This tests the handoff, not universal availability of the pair. -/
theorem pair_spend_at_pending_content
    {start gram land ind afterColon : SurfPos} {own n : Nat}
    {sc next : ScannerState}
    (markBack : ∀ outer, outer ∈ RegisterWitness.markedCols next →
      outer ∈ RegisterWitness.markedCols sc)
    (paired : ∀ outer ∈ RegisterWitness.markedCols sc, outer ≠ own →
      ∀ m : SurfPos, SSLComments gram m →
        ∀ e : SurfPos, SCompactSeqTail n m e →
          PairedExplicitValueLine start own outer e)
    (hssl : SSLComments gram land)
    (hind : SIndent own land ind) (hlit : GLit ':' ind afterColon) :
    ∀ outer ∈ RegisterWitness.markedCols next, outer ≠ own →
      ∀ m : SurfPos, SBlockIndented own .blockOut afterColon m →
        ExplValueLine start outer m := by
  intro outer hm hne m hval
  exact paired outer (markBack outer hm) hne land hssl land
    (SCompactSeqTail.nil n land) ind afterColon hind hlit m hval

#print axioms pair_at_question
#print axioms pair_at_landed_sequence
#print axioms pair_at_pending_content
#print axioms pair_spend_at_pending_content

end L4YAML.Proofs.StreamAccum
