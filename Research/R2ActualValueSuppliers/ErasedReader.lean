import Research.R2ActualValueSuppliers.Witness

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.PendingKeySound
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.CharPredicates R2ConcreteSuppliers R2ConcreteSequences
open R2JointFrames R2ActualJointStep R2MandatoryContext
open R2ActualValueSuppliers R2ActualValueWitness

-- The real reader call is identical to the accepted sibling writer except
-- that its retained Context is erased to its completed-stream projection.
example : Node s7 (SLYamlStream (pos 0 0)) 5 (pos 15 6) := by
  apply actual_same_implicit (s := dispatchState p6) (own := 4)
    (land := pos 9 0) (key := pos 13 4) (keyEnd := pos 14 5) (colon := pos 14 5)
    (step := by decide +kernel) (flow := by decide +kernel)
    (sound := sound_p6)
    (mono := (show MonoCheck (dispatchState p6) from by unfold MonoCheck; decide +kernel).sound)
    (base := by unfold IndentStackBase.SentinelBase; decide +kernel)
    (possible := by decide +kernel) (column := by decide +kernel) (same := by decide +kernel)
    (context := (context_dispatch (context_preprocess
      (by decide +kernel : scanNextToken_preprocess s6 = .ok (some (p6,':'))) after_key_c)).close)
  · exact SIndent.succ 3 _ 0 _ (SIndent.succ 2 _ 1 _
      (SIndent.succ 1 _ 2 _ (SIndent.succ 0 _ 3 _ (SIndent.zero _))))
  · exact ImplicitKeyHead.yaml (SNsPlainOneLine.mk .blockKey _ _ _
      (SNsPlainFirst.nonIndicator .blockKey 'c' _ 4
        (by unfold isNsPlainSafe isNsChar; decide) (by decide)) (GStar.nil _))
  · exact GStar.nil _
  · exact GLit.mk _ 5
