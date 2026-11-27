import Research.R2ConsumptionClosure.EntryValues

set_option autoImplicit false
open L4YAML L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.R2ConsumptionClosure
open L4YAML.Proofs.IndentStackCover (FrameLevel)

namespace R2ColonTailFrames

-- Keep the consumed entry's mapping open too: future siblings pass through
-- its actual compact tail before the surviving entries' context is resumed.
-- P may be EntryValues over the surviving marks; closing this frame with nil
-- recovers colon_value_domain, while this form also retains non-nil tails.
lemma colon_value_frames {P : SurfPos → Prop} {n : Nat} {keyEnd i colon : SurfPos}
    (step : EntryStep P n keyEnd) (indent : SIndent n keyEnd i)
    (literal : GLit ':' i colon) :
    ∀ e, SBlockNode (n + 1) .blockIn colon e → KeyFrames P [FrameLevel.map n] e := by
  intro e node
  exact KeyFrames.mapLevel n [] e (by simp) (fun z tail =>
    KeyFrames.bottom z (step.2 i colon indent literal e
      (SBlockIndented.node n .blockOut colon e
        (L4YAML.Proofs.NodeProduction.SBlockNode_blockIn_to_blockOut node)) z tail))

#print axioms colon_value_frames

end R2ColonTailFrames
