/- Closed native first implicit-map key/value consumer. Every native
edge is checked; this is not the global scanner induction. Capstone 7.7. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.MapReturn
public import Tests.Guards.Proofs.RightWallContentNative
public meta import L4YAML.Proofs.Serialization.TraceOf.MapReturn
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.MapReturnNative
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.Serialization.TraceOf.FlowReturn
open L4YAML.Proofs.Serialization.TraceOf.MapReturn
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
open L4YAML.Proofs.Serialization.TraceOf.RightWallContent
open L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
open L4YAML.Proofs.Serialization.TraceOf.RightWallRoute (DirectiveRoute)
open L4YAML.Proofs.StreamAccum (FrameTail)
def input : String := "a: [b]\n...\n%YAML 1.2\n---\ny"
def seed := scanSeed input
/-- Captured states are validated by independent native edge equations. -/
def keyPrep : ScannerState :=
  { seed with
    tokens := ((seed.tokens).push (RightWallContentNative.tokenAt 0 0 0 .placeholder)).push
      (RightWallContentNative.tokenAt 0 0 0 .placeholder),
    simpleKey := { possible := true, tokenIndex := 1, pos := ⟨0, 0, 0⟩, endLine := 0 },
    needIndentCheck := false }
def keyed : ScannerState :=
  { keyPrep with
    offset := 1,
    col := 1,
    tokens := (keyPrep.tokens).push ({ pos := { offset := 0, line := 0, col := 0 }, val := L4YAML.YamlToken.scalar "a" (L4YAML.ScalarStyle.plain), endPos := { offset := 0, line := 0, col := 0 } }),
    simpleKeyAllowed := false,
    allowDirectives := false,
    documentEverStarted := true }
def colonPrep := keyed
def coloned : ScannerState :=
  { colonPrep with
    offset := 2,
    col := 2,
    indents := #[{ column := -1, isSequence := false }, { column := 0, isSequence := false }],
    pendingKeys := #[none, none],
    tokens := (((colonPrep.tokens).setIfInBounds 1 ({ pos := { offset := 0, line := 0, col := 0 }, val := L4YAML.YamlToken.blockMappingStart, endPos := { offset := 0, line := 0, col := 0 } })).setIfInBounds 2 ({ pos := { offset := 0, line := 0, col := 0 }, val := L4YAML.YamlToken.key, endPos := { offset := 0, line := 0, col := 0 } })).push ({ pos := { offset := 1, line := 0, col := 1 }, val := L4YAML.YamlToken.value, endPos := { offset := 1, line := 0, col := 1 } }),
    simpleKey := { possible := false, tokenIndex := 0, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    simpleKeyAllowed := true,
    implicitValueLine := some 0 }
def openPrep : ScannerState :=
  { coloned with
    offset := 3,
    col := 3,
    tokens := ((coloned.tokens).push ({ pos := { offset := 3, line := 0, col := 3 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 3, line := 0, col := 3 } })).push ({ pos := { offset := 3, line := 0, col := 3 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 3, line := 0, col := 3 } }),
    simpleKey := { possible := true, tokenIndex := 5, pos := { offset := 3, line := 0, col := 3 }, endLine := 0 } }
def opened : ScannerState :=
  { openPrep with
    offset := 4,
    col := 4,
    flowLevel := 1,
    tokens := (openPrep.tokens).push ({ pos := { offset := 3, line := 0, col := 3 }, val := L4YAML.YamlToken.flowSequenceStart, endPos := { offset := 3, line := 0, col := 3 } }),
    simpleKey := { possible := false, tokenIndex := 0, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    simpleKeyStack := #[{ possible := true, tokenIndex := 5, pos := { offset := 3, line := 0, col := 3 }, endLine := 0 }],
    flowStack := #[true],
    explicitKeyStack := #[(none, -1)] }
def nodePrep : ScannerState :=
  { opened with
    tokens := ((opened.tokens).push ({ pos := { offset := 4, line := 0, col := 4 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 4, line := 0, col := 4 } })).push ({ pos := { offset := 4, line := 0, col := 4 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 4, line := 0, col := 4 } }),
    simpleKey := { possible := true, tokenIndex := 8, pos := { offset := 4, line := 0, col := 4 }, endLine := 0 } }
def content : ScannerState :=
  { nodePrep with
    offset := 5,
    col := 5,
    tokens := (nodePrep.tokens).push ({ pos := { offset := 4, line := 0, col := 4 }, val := L4YAML.YamlToken.scalar "b" (L4YAML.ScalarStyle.plain), endPos := { offset := 4, line := 0, col := 4 } }),
    simpleKeyAllowed := false }
def closePrep := content
def closed : ScannerState :=
  { closePrep with
    offset := 6,
    col := 6,
    flowLevel := 0,
    tokens := (closePrep.tokens).push ({ pos := { offset := 5, line := 0, col := 5 }, val := L4YAML.YamlToken.flowSequenceEnd, endPos := { offset := 5, line := 0, col := 5 } }),
    simpleKey := { possible := true, tokenIndex := 5, pos := { offset := 3, line := 0, col := 3 }, endLine := 0 },
    simpleKeyStack := #[],
    flowStack := #[],
    explicitKeyStack := #[] }
def endPrep : ScannerState :=
  { closed with
    offset := 7,
    line := 1,
    col := 0,
    tokens := ((closed.tokens).push ({ pos := { offset := 7, line := 1, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 7, line := 1, col := 0 } })).push ({ pos := { offset := 7, line := 1, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 7, line := 1, col := 0 } }),
    simpleKey := { possible := true, tokenIndex := 12, pos := { offset := 7, line := 1, col := 0 }, endLine := 1 },
    simpleKeyAllowed := true }
def ended : ScannerState :=
  { endPrep with
    offset := 10,
    col := 3,
    indents := #[{ column := -1, isSequence := false }],
    pendingKeys := #[none],
    tokens := ((endPrep.tokens).push ({ pos := { offset := 7, line := 1, col := 0 }, val := L4YAML.YamlToken.blockEnd, endPos := { offset := 7, line := 1, col := 0 } })).push ({ pos := { offset := 7, line := 1, col := 0 }, val := L4YAML.YamlToken.documentEnd, endPos := { offset := 7, line := 1, col := 0 } }),
    simpleKey := { possible := false, tokenIndex := 0, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    allowDirectives := true }
def dirPrep : ScannerState :=
  { ended with
    offset := 11,
    line := 2,
    col := 0,
    tokens := ((ended.tokens).push ({ pos := { offset := 11, line := 2, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 11, line := 2, col := 0 } })).push ({ pos := { offset := 11, line := 2, col := 0 }, val := L4YAML.YamlToken.placeholder, endPos := { offset := 11, line := 2, col := 0 } }),
    simpleKey := { possible := true, tokenIndex := 16, pos := { offset := 11, line := 2, col := 0 }, endLine := 2 } }
def directed : ScannerState :=
  { dirPrep with
    offset := 20,
    col := 9,
    tokens := (dirPrep.tokens).push ({ pos := { offset := 11, line := 2, col := 0 }, val := L4YAML.YamlToken.versionDirective "1".toNat! "2".toNat!, endPos := { offset := 11, line := 2, col := 0 } }),
    seenYamlDirective := true,
    directivesPresent := true }

def keyAd : ScannerState := { keyPrep with allowDirectives := false, documentEverStarted := true }
def start : SurfPos := ⟨input.toList, 0⟩
def keyEnd : SurfPos := ⟨": [b]\n...\n%YAML 1.2\n---\ny".toList, 1⟩
def mapPos : SurfPos := ⟨" [b]\n...\n%YAML 1.2\n---\ny".toList, 2⟩
def root : SurfPos := ⟨"[b]\n...\n%YAML 1.2\n---\ny".toList, 3⟩
def openPos : SurfPos := ⟨"b]\n...\n%YAML 1.2\n---\ny".toList, 4⟩
def nodeEnd : SurfPos := ⟨"]\n...\n%YAML 1.2\n---\ny".toList, 5⟩
def closePos : SurfPos := ⟨"\n...\n%YAML 1.2\n---\ny".toList, 6⟩
def endPos : SurfPos := ⟨"...\n%YAML 1.2\n---\ny".toList, 0⟩
def dirPos : SurfPos := ⟨"%YAML 1.2\n---\ny".toList, 0⟩
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
lemma step_keyed : scanNextToken seed = .ok (some keyed) := by cbv
lemma step_coloned : scanNextToken keyed = .ok (some coloned) := by cbv
lemma step_opened : scanNextToken coloned = .ok (some opened) := by cbv
lemma step_content : scanNextToken opened = .ok (some content) := by cbv
lemma step_closed : scanNextToken content = .ok (some closed) := by cbv
lemma step_ended : scanNextToken closed = .ok (some ended) := by cbv
lemma step_directed : scanNextToken ended = .ok (some directed) := by cbv
lemma dispatch_key : scanNextToken_dispatchContent keyAd 'a' = .ok keyed := by cbv
lemma pre_colon : scanNextToken_preprocess keyed = .ok (some (colonPrep, ':')) := by cbv
lemma dispatch_colon : scanNextToken_dispatchBlockIndicators colonPrep ':' = .ok (some coloned) := by cbv
lemma dispatch_content : scanNextToken_dispatchContent nodePrep 'b' = .ok content := by cbv
lemma dispatch_end : scanDocumentEnd endPrep = .ok ended := by cbv
lemma dispatch_dir : scanDirective dirPrep = .ok directed := by cbv

lemma corr_key : ScannerSurfCorr keyPrep start := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "".toList ++ start.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "".toList h
    have hOffset : 0 + listByteSize "".toList = keyPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma corr_colon : ScannerSurfCorr colonPrep keyEnd := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"a".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "a".toList ++ keyEnd.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "a".toList h
    have hOffset : 0 + listByteSize "a".toList = colonPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma corr_map : ScannerSurfCorr coloned mapPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"a:".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "a:".toList ++ mapPos.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "a:".toList h
    have hOffset : 0 + listByteSize "a:".toList = coloned.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst i
    change (0 : Int) ≥ 0
    omega

lemma corr_open : ScannerSurfCorr openPrep root := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"a: ".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "a: ".toList ++ root.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "a: ".toList h
    have hOffset : 0 + listByteSize "a: ".toList = openPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst i
    change (0 : Int) ≥ 0
    omega

lemma corr_node : ScannerSurfCorr nodePrep openPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"a: [".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "a: [".toList ++ openPos.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "a: [".toList h
    have hOffset : 0 + listByteSize "a: [".toList = nodePrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst i
    change (0 : Int) ≥ 0
    omega

lemma corr_close : ScannerSurfCorr closePrep nodeEnd := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"a: [b".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "a: [b".toList ++ nodeEnd.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "a: [b".toList h
    have hOffset : 0 + listByteSize "a: [b".toList = closePrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst i
    change (0 : Int) ≥ 0
    omega

lemma corr_end : ScannerSurfCorr endPrep endPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"a: [b]\n".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "a: [b]\n".toList ++ endPos.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "a: [b]\n".toList h
    have hOffset : 0 + listByteSize "a: [b]\n".toList = endPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst i
    change (0 : Int) ≥ 0
    omega

lemma corr_dir : ScannerSurfCorr dirPrep dirPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"a: [b]\n...\n".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "a: [b]\n...\n".toList ++ dirPos.chars := by cbv
    rw [hSplit] at h
    have ht := RightWallContentNative.chars_drop input "a: [b]\n...\n".toList h
    have hOffset : 0 + listByteSize "a: [b]\n...\n".toList = dirPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega

lemma native_directive_after_implicit_mapping :
    ScannerReachable input directed ∧
    ∃ stop, ScannerSurfCorr directed stop ∧
      TSLYamlStream start directed dirPos [.endDocument] []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirPos stop)).toList ∧
      TPendingNode start true dirPos stop [.endDocument] []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirPos stop)).toList ∧
      DirectiveRoute start dirPos [.endDocument] := by
  have hr0 : ScannerReachable input seed := .seed
  have hr1 := hr0.step step_keyed
  have hr2 := hr1.step step_coloned
  have hr3 := hr2.step step_opened
  have hr4 := hr3.step step_content
  have hr5 := hr4.step step_closed
  have hr6 := hr5.step step_ended
  have hr7 := hr6.step step_directed
  refine ⟨hr7, ?_⟩
  have hSeed : TSLYamlStream start seed start [] [] [] :=
    TSLYamlStream.seed input.toList seed (seed_tokens_only_streamStart input)
  have hAd : ScannerSurfCorr keyAd start :=
    L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update corr_key
  obtain ⟨keyEvents, hKey, hPushKey⟩ := implicit_key_of_dispatch hAd
    (show ScannerSurfCorr keyed keyEnd from corr_colon)
    (by cbv) dispatch_key (by cbv) (by cbv) (by cbv) (by cbv)
    (by intro _; cbv) (by decide) (by decide)
  have hKeyTrace : TSLYamlStream start keyed start [] keyEvents [] :=
    ⟨hSeed.stream, by
      rw [hPushKey.goOut_at []]
      have ht : goOut keyAd.tokens.toList [] = ([], []) := by cbv
      rw [ht]⟩
  have hKeyEvents : keyEvents = [] := by
    have h := hKeyTrace.events
    have ht : goOut keyed.tokens.toList [] = ([], []) := by cbv
    rw [ht] at h
    simpa using congrArg Prod.fst h.symm
  subst keyEvents
  obtain ⟨valuePos, hcValue, hMapTrace, hMapClose, hMapPending⟩ := first_implicit_colon
    (input := input) (sc := keyed) (prep := colonPrep) (after := coloned)
    (start := start) (line := start) (key := start) (scan := keyEnd) (colonPos := keyEnd)
    (k := 0) (events := []) hr1 hKeyTrace hKey (.nil _) (by cbv) (.zero _)
    pre_colon (.nil _) corr_colon (by simpa only [show colonPrep.allowDirectives = false from by cbv, Bool.false_eq_true, if_false] using dispatch_colon)
  have hValue : valuePos = mapPos := ScannerSurfCorr_unique hcValue corr_map
  subst valuePos
  have hSep : SSeparate 1 .flowOut mapPos root :=
    .inline 1 _ _ (.whites _ _ (.mk _ _ _ (.space _ 2) (.nil _)))
  have hFunded := return_map_value (k := 0) hMapClose hSep
  obtain ⟨op, htOpen, hcOpen, hOpen⟩ := FlowBridge.scanFlowSequenceStart_trace
    openPrep root corr_open (by cbv)
  have hOp : op = openPos := by cases hOpen.1; rfl
  subst op
  have hRoot : FlowOpenR 1 (StreamReturn start []) 1 #[true] #[false]
      .sep start openPos [] :=
    .seqBase start root openPos openPos openPos .sep [] hOpen.1
      (.none _) (.betweenEmpty _) hFunded
  obtain ⟨landing, hArm⟩ := L4YAML.Proofs.StreamAccum.contentArm_of_dispatch
    nodePrep openPos 'b' corr_node (by cbv) (by intro _; cbv)
    (by intro _; change (0 : Int) < 4; omega) dispatch_content
  have hLanding : landing = nodeEnd := by
    have hc : ScannerSurfCorr content landing := by cases hArm <;> assumption
    have he : content = closePrep := by cbv
    rw [he] at hc
    exact ScannerSurfCorr_unique hc corr_close
  subst landing
  obtain ⟨ev, hPush, hReceived⟩ := accum_step_content_return_in (n := 1) (D := 1)
    (ks := #[true]) (km := #[false]) (sp_block := start) (sp_flow := openPos) (ev := [])
    (Return := StreamReturn start []) hArm corr_node (by cbv) (by cbv) (by intro _; cbv)
    dispatch_content (by change (0 : Int) < 4; omega) (by change (1 : Int) ≤ max 0 1; omega)
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
  · obtain ⟨stop, htClose, hcClose, hClose⟩ := FlowBridge.scanFlowSequenceEnd_trace
      closePrep nodeEnd corr_close (by cbv)
    have hStop : stop = closePos := by cases hClose.1; rfl
    subst stop
    have hLead : SSeparateLines 1 grammarEnd nodeEnd ∨
        (nodeEnd = grammarEnd ∧ (FrameTail.value kj).closeFree = true) := by
      cases hw with
      | nil => exact Or.inr ⟨rfl, rfl⟩
      | cons a b z one rest => exact Or.inl (.inline _ _ _ (.whites _ _ (.mk _ _ _ one rest)))
    have hReturn : StreamReturn start [] closePos [] := by
      simpa using hStack.closeSeqBase hLead hClose.1
    have hTrace : TSLYamlStream start closed start [] [] [] :=
      ⟨hMapTrace.stream, by cbv⟩
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

#print axioms L4YAML.Tests.Guards.MapReturnNative.native_directive_after_implicit_mapping
end L4YAML.Tests.Guards.MapReturnNative
end Blanket
