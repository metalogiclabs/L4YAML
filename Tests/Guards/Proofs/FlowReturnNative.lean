/- A closed native flow path exercises the funded return at the actual
pending-document/directive consumer. It does not establish the global fold. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.FlowReturn
public import Tests.Guards.Proofs.RightWallContentNative
public meta import L4YAML.Proofs.Serialization.TraceOf.FlowReturn

@[expose] public section Blanket
namespace L4YAML.Tests.Guards.FlowReturnNative
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.Serialization.TraceOf.FlowReturn
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
open L4YAML.Proofs.Serialization.TraceOf.RightWallContent
open L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
open L4YAML.Proofs.Serialization.TraceOf.RightWallRoute (DirectiveRoute)
open L4YAML.Proofs.StreamAccum (FrameTail)

def input : String := "[a]\n...\n%YAML 1.2\n---\ny"
def seed := scanSeed input
/-- Captured states, independently checked by each scanNextToken equality. -/
def openPrep : ScannerState :=
  { seed with
    tokens := ((seed.tokens).push (RightWallContentNative.tokenAt 0 0 0 .placeholder)).push
      (RightWallContentNative.tokenAt 0 0 0 .placeholder),
    simpleKey := { possible := true, tokenIndex := 1, pos := ⟨0, 0, 0⟩, endLine := 0 },
    needIndentCheck := false }
def opened : ScannerState :=
  { openPrep with
    offset := 1,
    col := 1,
    flowLevel := 1,
    tokens := (openPrep.tokens).push ({ pos := { offset := 0, line := 0, col := 0 }, val := L4YAML.YamlToken.flowSequenceStart, endPos := { offset := 0, line := 0, col := 0 } }),
    simpleKey := { possible := false, tokenIndex := 0, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    simpleKeyStack := #[{ possible := true, tokenIndex := 1, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 }],
    allowDirectives := false,
    documentEverStarted := true,
    flowStack := #[true],
    explicitKeyStack := #[(none, -1)] }
def nodePrep : ScannerState :=
  { opened with
    tokens := ((opened.tokens).push ({ pos := { offset := 1, line := 0, col := 1 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 1, line := 0, col := 1 } })).push ({ pos := { offset := 1, line := 0, col := 1 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 1, line := 0, col := 1 } }),
    simpleKey := { possible := true, tokenIndex := 4, pos := { offset := 1, line := 0, col := 1 }, endLine := 0 } }
def content : ScannerState :=
  { nodePrep with
    offset := 2,
    col := 2,
    tokens := (nodePrep.tokens).push ({ pos := { offset := 1, line := 0, col := 1 }, val := L4YAML.YamlToken.scalar "a" (L4YAML.ScalarStyle.plain), endPos := { offset := 1, line := 0, col := 1 } }),
    simpleKeyAllowed := false }
def closePrep : ScannerState :=
  { content with
     }
def closed : ScannerState :=
  { closePrep with
    offset := 3,
    col := 3,
    flowLevel := 0,
    tokens := (closePrep.tokens).push ({ pos := { offset := 2, line := 0, col := 2 }, val := L4YAML.YamlToken.flowSequenceEnd, endPos := { offset := 2, line := 0, col := 2 } }),
    simpleKey := { possible := true, tokenIndex := 1, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    simpleKeyStack := #[],
    flowStack := #[],
    explicitKeyStack := #[] }
def endPrep : ScannerState :=
  { closed with
    offset := 4,
    line := 1,
    col := 0,
    tokens := ((closed.tokens).push ({ pos := { offset := 4, line := 1, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 4, line := 1, col := 0 } })).push ({ pos := { offset := 4, line := 1, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 4, line := 1, col := 0 } }),
    simpleKey := { possible := true, tokenIndex := 8, pos := { offset := 4, line := 1, col := 0 }, endLine := 1 },
    simpleKeyAllowed := true }
def ended : ScannerState :=
  { endPrep with
    offset := 7,
    col := 3,
    tokens := (endPrep.tokens).push ({ pos := { offset := 4, line := 1, col := 0 }, val := L4YAML.YamlToken.documentEnd, endPos := { offset := 4, line := 1, col := 0 } }),
    simpleKey := { possible := false, tokenIndex := 0, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    allowDirectives := true }
def dirPrep : ScannerState :=
  { ended with
    offset := 8,
    line := 2,
    col := 0,
    tokens := ((ended.tokens).push ({ pos := { offset := 8, line := 2, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 8, line := 2, col := 0 } })).push ({ pos := { offset := 8, line := 2, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 8, line := 2, col := 0 } }),
    simpleKey := { possible := true, tokenIndex := 11, pos := { offset := 8, line := 2, col := 0 }, endLine := 2 } }
def directed : ScannerState :=
  { dirPrep with
    offset := 17,
    col := 9,
    tokens := (dirPrep.tokens).push ({ pos := { offset := 8, line := 2, col := 0 }, val := L4YAML.YamlToken.versionDirective "1".toNat! "2".toNat!, endPos := { offset := 8, line := 2, col := 0 } }),
    seenYamlDirective := true,
    directivesPresent := true }

def start : SurfPos := ⟨input.toList, 0⟩
def openPos : SurfPos := ⟨"a]\n...\n%YAML 1.2\n---\ny".toList, 1⟩
def nodeEnd : SurfPos := ⟨"]\n...\n%YAML 1.2\n---\ny".toList, 2⟩
def closePos : SurfPos := ⟨"\n...\n%YAML 1.2\n---\ny".toList, 3⟩
def endPos : SurfPos := ⟨"...\n%YAML 1.2\n---\ny".toList, 0⟩
def dirPos : SurfPos := ⟨"%YAML 1.2\n---\ny".toList, 0⟩

set_option maxRecDepth 20000
set_option maxHeartbeats 800000
lemma step_opened : scanNextToken seed = .ok (some opened) := by cbv
lemma step_content : scanNextToken opened = .ok (some content) := by cbv
lemma step_closed : scanNextToken content = .ok (some closed) := by cbv
lemma step_ended : scanNextToken closed = .ok (some ended) := by cbv
lemma step_directed : scanNextToken ended = .ok (some directed) := by cbv
lemma dispatch_content : scanNextToken_dispatchContent nodePrep 'a' = .ok content := by cbv
lemma dispatch_end : scanDocumentEnd endPrep = .ok ended := by cbv
lemma dispatch_dir : scanDirective dirPrep = .ok directed := by cbv

lemma corr_open : ScannerSurfCorr openPrep start := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "".toList ++ start.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "".toList h
    have hOffset : 0 + listByteSize "".toList = openPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma corr_node : ScannerSurfCorr nodePrep openPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"[".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "[".toList ++ openPos.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "[".toList h
    have hOffset : 0 + listByteSize "[".toList = nodePrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma corr_close : ScannerSurfCorr closePrep nodeEnd := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"[a".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "[a".toList ++ nodeEnd.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "[a".toList h
    have hOffset : 0 + listByteSize "[a".toList = closePrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma corr_end : ScannerSurfCorr endPrep endPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"[a]\n".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "[a]\n".toList ++ endPos.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "[a]\n".toList h
    have hOffset : 0 + listByteSize "[a]\n".toList = endPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma corr_dir : ScannerSurfCorr dirPrep dirPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"[a]\n...\n".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "[a]\n...\n".toList ++ dirPos.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "[a]\n...\n".toList h
    have hOffset : 0 + listByteSize "[a]\n...\n".toList = dirPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma native_directive_after_flow :
    ScannerReachable input directed ∧
    ∃ stop, ScannerSurfCorr directed stop ∧
      TSLYamlStream start directed dirPos [.endDocument] []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirPos stop)).toList ∧
      TPendingNode start true dirPos stop [.endDocument] []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirPos stop)).toList ∧
      DirectiveRoute start dirPos [.endDocument] := by
  have hr : ScannerReachable input seed := .seed
  have hr := hr.step step_opened
  have hr := hr.step step_content
  have hr := hr.step step_closed
  have hr := hr.step step_ended
  have hr := hr.step step_directed
  refine ⟨hr, ?_⟩
  obtain ⟨op, _, hCorrOp, hOpen⟩ := FlowBridge.scanFlowSequenceStart_trace
    openPrep start corr_open (by cbv)
  have hOp : op = openPos := by
    cases hOpen.1
    rfl
  subst op
  have hRoot : FlowOpenR 0 (StreamReturn start []) 1 #[true] #[false]
      .sep start openPos [] :=
    .seqBase start start openPos openPos openPos .sep [] hOpen.1
      (.none _) (.betweenEmpty _) (return_first (.nil _) (.inline _ _ _ (.startOfLine _)))
  obtain ⟨landing, hArm⟩ := L4YAML.Proofs.StreamAccum.contentArm_of_dispatch
    nodePrep openPos 'a' corr_node (by cbv) (by intro _; cbv)
    (by intro _; change (-1 : Int) < 1; omega) dispatch_content
  have hLanding : landing = nodeEnd := by
    have hc : ScannerSurfCorr content landing := by cases hArm <;> assumption
    have he : content = closePrep := by cbv
    rw [he] at hc
    exact ScannerSurfCorr_unique hc corr_close
  subst landing
  obtain ⟨ev, hPush, hReceived⟩ := accum_step_content_return_in (n := 0) (D := 1) (ks := #[true]) (km := #[false])
    (sp_block := start) (sp_flow := openPos) (ev := [])
    (Return := StreamReturn start []) hArm corr_node (by cbv)
    (by cbv) (by intro _; cbv) dispatch_content (by change (-1 : Int) < 1; omega) (by change (0 : Int) ≤ max 0 0; omega)
    (by simpa only [show L4YAML.Proofs.StreamAccum.tailOf nodePrep.tokens = FrameTail.sep from by cbv] using hRoot)
    (by intro kj; rw [show L4YAML.Proofs.StreamAccum.tailOf nodePrep.tokens = FrameTail.sep from by cbv]; nofun)
    (Or.inr ⟨rfl, by rw [show L4YAML.Proofs.StreamAccum.tailOf nodePrep.tokens = FrameTail.sep from by cbv]; rfl⟩)
  have hEv : ev = [] := by
    have h := hPush.goOut_at []
    have hBefore : goOut nodePrep.tokens.toList [] = ([], []) := by cbv
    have hAfter : goOut content.tokens.toList [] = ([], []) := by cbv
    rw [hBefore, hAfter] at h
    simpa using congrArg Prod.fst h.symm
  subst ev
  rcases hReceived with ⟨kj, grammarEnd, ht, hw, _, hStack, _⟩ | hProp
  · obtain ⟨stop, _, hCloseCorr, hClose⟩ := FlowBridge.scanFlowSequenceEnd_trace
      closePrep nodeEnd corr_close (by cbv)
    have hStop : stop = closePos := by cases hClose.1; rfl
    subst stop
    have hLead : SSeparateLines 0 grammarEnd nodeEnd ∨
        (nodeEnd = grammarEnd ∧ (FrameTail.value kj).closeFree = true) := by
      cases hw with
      | nil => exact Or.inr ⟨rfl, rfl⟩
      | cons a b z one rest =>
        exact Or.inl (.inline _ _ _ (.whites _ _ (.mk _ _ _ one rest)))
    have hReturn : StreamReturn start [] closePos [] := by
      simpa using hStack.closeSeqBase hLead hClose.1
    have hTrace : TSLYamlStream start closed start [] [] [] :=
      ⟨(TSLYamlStream.seed input.toList seed (seed_tokens_only_streamStart input)).stream, by cbv⟩
    obtain ⟨stop, hc, hs, hp⟩ := directive_after_pending_document
      (start := start) (block := start) (scan := closePos)
      (endLanding := endPos) (dirLanding := dirPos)
      (sc := closed) (endPrep := endPrep) (ended := ended)
      (dirPrep := dirPrep) (directed := directed) (c := '.')
      (ev_c := []) (ev_o := []) hTrace (returned_pending hReturn)
      (by cbv)
      (.withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _))
      corr_end "\n%YAML 1.2\n---\ny".toList (by cbv) (by cbv) dispatch_end
      (by cbv)
      (.withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _))
      (by cbv) corr_dir (by cbv) dispatch_dir
    have hRoute : DirectiveRoute start dirPos [.endDocument] := by
      cases hp with | pendingDirective _ _ _ _ h _ => exact h
    exact ⟨stop, hc, hs, hp, hRoute⟩
  · rcases hProp.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> contradiction

#print axioms L4YAML.Tests.Guards.FlowReturnNative.native_directive_after_flow
end L4YAML.Tests.Guards.FlowReturnNative
end Blanket
