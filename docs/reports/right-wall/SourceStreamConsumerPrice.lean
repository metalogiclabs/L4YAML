/- Price only: the type and body of the first actual bare-document consumer
   are copied unchanged from upstream 14eb6dba StreamAccum.topLevelFlowResumeSep.
   Compile once against the original Surface.Document, then against the
   isolated explicit-document-only constructor. This is not a repaired lemma. -/
module
public import L4YAML.Surface.Document
@[expose] public section Blanket
namespace L4YAML.Proofs.StreamAccum
open L4YAML L4YAML.Surface

lemma topLevelFlowResumeSep {sp_start sp_mid sp_br : SurfPos}
    (h_stream : SLYamlStream sp_start sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_br) :
    ∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m :=
  fun sp_ne sp_m h_content h_ssl =>
    SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_m sp_m
      h_stream (GStar.nil _)
      (GOpt.some sp_mid sp_m
        (SLAnyDocument.bare sp_mid sp_m
          (SLBareDocument.mk sp_mid sp_m
            (SBlockNode.flowInBlock 0 .blockIn sp_mid sp_br sp_ne sp_m
              h_sep (SFlowNode.content _ _ _ _ h_content) h_ssl))))
      (GStar.nil _)

end L4YAML.Proofs.StreamAccum
end Blanket
