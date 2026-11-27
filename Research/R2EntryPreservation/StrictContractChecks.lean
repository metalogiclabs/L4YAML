import L4YAML.Proofs.Production.StreamAccum

set_option autoImplicit false
open L4YAML L4YAML.Surface L4YAML.Scanner
open L4YAML.Proofs.StreamAccum L4YAML.Proofs

def StrictKeyPairAt (sc : ScannerState) (start gram : SurfPos) (own : Nat) : Prop :=
  ∀ outer ∈ RegisterWitness.markedCols sc, outer < own →
    ∀ mid i c, SSLComments gram mid → SIndent own mid i → GLit ':' i c →
    ∀ v, SBlockIndented own .blockOut c v → ExplValueLine start outer v

-- This is the exact post-landing boundary needed by the colon consumer.
-- The strict bound follows from the real output stack and consumed-own mark,
-- rather than from an assumption that every different mark is an ancestor.
lemma strictPairAt_landing {before after : ScannerState}
    {start gram mid ind colon : SurfPos} {own : Nat}
    (mono : IndentStackMono.Mono after)
    (top : after.currentIndent ≤ (own : Int))
    (consumed : own ∉ RegisterWitness.markedCols after)
    (back : ∀ a ∈ RegisterWitness.markedCols after, a ∈ RegisterWitness.markedCols before)
    (pair : StrictKeyPairAt before start gram own)
    (comments : SSLComments gram mid) (indent : SIndent own mid ind)
    (literal : GLit ':' ind colon) :
    ∀ a ∈ RegisterWitness.markedCols after,
      ∀ v, SBlockIndented own .blockOut colon v → ExplValueLine start a v := by
  intro a ha v value
  have le := markedCols_le_of_top mono top a ha
  have ne : a ≠ own := fun h => consumed (h ▸ ha)
  have lt : a < own := by omega
  exact pair a (back a ha) lt mid ind colon comments indent literal v value

#print axioms strictPairAt_landing
