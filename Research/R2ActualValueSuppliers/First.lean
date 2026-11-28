import Research.R2ActualValueSuppliers.Producers

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.PendingKeySound
open R2JointFrames R2ActualJointStep R2MandatoryContext

namespace R2ActualValueSuppliers

lemma actual_first_keyless {s t : ScannerState} {start land colon next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (negative : s.currentIndent < 0)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land colon) (literal : GLit ':' colon next) :
    Node t (SLYamlStream start) (own+1) next :=
  actual_first_value step flow sound mono base possible column negative lineStart prefixes indent
    (fun e node => SBlockMapEntry.emptyKeyNode own colon next e literal
      (SBlockNode_blockIn_to_blockOut node))

lemma actual_first_implicit {s t : ScannerState}
    {start land key keyEnd colon next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (negative : s.currentIndent < 0)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land key) (head : ImplicitKeyHead key keyEnd)
    (white : GStar SSWhite keyEnd colon) (literal : GLit ':' colon next) :
    Node t (SLYamlStream start) (own+1) next :=
  actual_first_value step flow sound mono base possible column negative lineStart prefixes indent
    (fun e node => SBlockMapEntry.implicitKeyNode own key colon next e
      (implicitKeyHead_to_SImplicitKey head white) literal
      (SBlockNode_blockIn_to_blockOut node))

lemma actual_first_properties {s t : ScannerState}
    {start land key keyEnd colon next : SurfPos} {own : Nat}
    (step : scanValue s = .ok t) (flow : s.inFlow = false)
    (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : IndentStackBase.SentinelBase s)
    (possible : (scanValueClearKey s).simpleKey.possible = true)
    (column : (scanValueClearKey s).simpleKey.pos.col = own)
    (negative : s.currentIndent < 0)
    (lineStart : land.col = 0) (prefixes : GStar SLDocumentPrefix start land)
    (indent : SIndent own land key) (props : SCNsProperties 0 .blockKey key keyEnd)
    (white : GStar SSWhite keyEnd colon) (literal : GLit ':' colon next) :
    Node t (SLYamlStream start) (own+1) next :=
  actual_first_value step flow sound mono base possible column negative lineStart prefixes indent
    (fun e node => SBlockMapEntry.implicitKeyNode own key colon next e
      (SImplicitKey.jsonKey key keyEnd colon (SFlowNode.propsEmpty 0 .blockKey key keyEnd props)
        (ScalarProduction.gstar_sswhite_to_gopt_sep white)) literal
      (SBlockNode_blockIn_to_blockOut node))

#print axioms actual_first_keyless
#print axioms actual_first_implicit
#print axioms actual_first_properties

end R2ActualValueSuppliers
