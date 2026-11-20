/- A closed native witness for the new content producer and its real directive
consumer. This finite case is not the global scanner induction. -/
module

public import L4YAML.Proofs.Serialization.TraceOf.RightWallContent
public import Tests.Guards.Proofs.RightWallReachability
public meta import L4YAML.Proofs.Serialization.TraceOf.RightWallContent

@[expose] public section Blanket
namespace L4YAML.Tests.Guards.RightWallContentNative
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
open L4YAML.Proofs.Serialization.TraceOf.RightWallContent
open L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
open L4YAML.Proofs.Serialization.TraceOf.RightWallRoute (DirectiveRoute)

def input : String := "---\nx\n...\n%YAML 1.2\n---\ny"
/-- Captured native states below are validated by the four executable
transition equalities in native_directive_after_explicit_scalar. -/
def tokenAt (offset line col : Nat) (val : YamlToken) : Positioned YamlToken :=
  { pos := ⟨offset, line, col⟩, val := val, endPos := ⟨offset, line, col⟩ }

def seed := scanSeed input

def markerPrep : ScannerState :=
  { seed with
    tokens := ((seed.tokens).push (tokenAt 0 0 0 (L4YAML.YamlToken.placeholder))).push (tokenAt 0 0 0 (L4YAML.YamlToken.placeholder)),
    simpleKey := { possible := true, tokenIndex := 1, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    needIndentCheck := false }

def started : ScannerState :=
  { markerPrep with
    offset := 3,
    col := 3,
    tokens := (markerPrep.tokens).push (tokenAt 0 0 0 (L4YAML.YamlToken.documentStart)),
    simpleKey := { possible := false, tokenIndex := 0, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    allowDirectives := false,
    documentEverStarted := true,
    docStartLine := some 0 }

def nodePrep : ScannerState :=
  { started with
    offset := 4,
    line := 1,
    col := 0,
    tokens := ((started.tokens).push (tokenAt 4 1 0 (L4YAML.YamlToken.placeholder))).push (tokenAt 4 1 0 (L4YAML.YamlToken.placeholder)),
    simpleKey := { possible := true, tokenIndex := 4, pos := { offset := 4, line := 1, col := 0 }, endLine := 1 } }

def content : ScannerState :=
  { nodePrep with
    offset := 5,
    col := 1,
    tokens := (nodePrep.tokens).push (tokenAt 4 1 0 (L4YAML.YamlToken.scalar "x" (L4YAML.ScalarStyle.plain))),
    simpleKeyAllowed := false }

def endPrep : ScannerState :=
  { content with
    offset := 6,
    line := 2,
    col := 0,
    tokens := ((content.tokens).push (tokenAt 6 2 0 (L4YAML.YamlToken.placeholder))).push (tokenAt 6 2 0 (L4YAML.YamlToken.placeholder)),
    simpleKey := { possible := true, tokenIndex := 7, pos := { offset := 6, line := 2, col := 0 }, endLine := 2 },
    simpleKeyAllowed := true }

def ended : ScannerState :=
  { endPrep with
    offset := 9,
    col := 3,
    tokens := (endPrep.tokens).push (tokenAt 6 2 0 (L4YAML.YamlToken.documentEnd)),
    simpleKey := { possible := false, tokenIndex := 0, pos := { offset := 0, line := 0, col := 0 }, endLine := 0 },
    allowDirectives := true }

def dirPrep : ScannerState :=
  { ended with
    offset := 10,
    line := 3,
    col := 0,
    tokens := ((ended.tokens).push (tokenAt 10 3 0 (L4YAML.YamlToken.placeholder))).push (tokenAt 10 3 0 (L4YAML.YamlToken.placeholder)),
    simpleKey := { possible := true, tokenIndex := 10, pos := { offset := 10, line := 3, col := 0 }, endLine := 3 } }

def directed : ScannerState :=
  { dirPrep with
    offset := 19,
    col := 9,
    tokens := (dirPrep.tokens).push (tokenAt 10 3 0 (L4YAML.YamlToken.versionDirective "1".toNat! "2".toNat!)),
    seenYamlDirective := true,
    directivesPresent := true }

def start : SurfPos := ⟨input.toList, 0⟩
def node : SurfPos := ⟨"\nx\n...\n%YAML 1.2\n---\ny".toList, 3⟩
def nodePos : SurfPos := ⟨"x\n...\n%YAML 1.2\n---\ny".toList, 0⟩
def contentPos : SurfPos := ⟨"\n...\n%YAML 1.2\n---\ny".toList, 1⟩
def endPos : SurfPos := ⟨"...\n%YAML 1.2\n---\ny".toList, 0⟩
def dirPos : SurfPos := ⟨"%YAML 1.2\n---\ny".toList, 0⟩

/-- Native edges and preprocess/dispatch equations, each kernel checked. -/
lemma step_started : scanNextToken seed = .ok (some started) := by cbv
lemma step_content : scanNextToken started = .ok (some content) := by cbv
lemma step_ended : scanNextToken content = .ok (some ended) := by cbv
lemma step_directed : scanNextToken ended = .ok (some directed) := by cbv
lemma pre_marker : scanNextToken_preprocess seed = .ok (some (markerPrep, '-')) := by cbv
lemma pre_node : scanNextToken_preprocess (scanDocumentStart markerPrep) =
    .ok (some (nodePrep, 'x')) := by cbv
lemma pre_end : scanNextToken_preprocess content = .ok (some (endPrep, '.')) := by cbv
lemma pre_dir : scanNextToken_preprocess ended = .ok (some (dirPrep, '%')) := by cbv
lemma dispatch_content : scanNextToken_dispatchContent nodePrep 'x' = .ok content := by cbv
lemma dispatch_end : scanDocumentEnd endPrep = .ok ended := by cbv
lemma dispatch_dir : scanDirective dirPrep = .ok directed := by cbv

/-- Reuse the native UTF-8 correspondence by removing a known prefix,
instead of rebuilding the entire character suffix one constructor at a time. -/
lemma chars_drop (src : String) (pre : List Char) :
    ∀ {p : Nat} {suf : List Char}, CharsFromOffset src p (pre ++ suf) →
      CharsFromOffset src (p + listByteSize pre) suf := by
  induction pre with
  | nil => intro p suf h; simpa [listByteSize] using h
  | cons ch rest ih =>
    intro p suf h
    have hg : String.Pos.Raw.get src ⟨p⟩ = ch := by
      cases h with | cons _ _ _ _ hg _ => exact hg
    have ht := chars_from_cons_tail h
    rw [next_byteIdx, hg] at ht
    simpa only [listByteSize, Nat.add_assoc] using ih ht

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
lemma corr_marker : ScannerSurfCorr markerPrep start := by
  refine ⟨?_, (by cbv), (by cbv), ⟨[], (by cbv), by cbv⟩, ?_⟩
  · exact chars_from_zero_toList input
  · intro i hi hpos
    change i < 1 at hi
    omega


set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
lemma corr_node : ScannerSurfCorr nodePrep nodePos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"---\n".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "---\n".toList ++ nodePos.chars := by cbv
    rw [hSplit] at h
    have ht := chars_drop input "---\n".toList h
    have hOffset : 0 + listByteSize "---\n".toList = nodePrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega


set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
lemma corr_content : ScannerSurfCorr content contentPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"---\nx".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "---\nx".toList ++ contentPos.chars := by cbv
    rw [hSplit] at h
    have ht := chars_drop input "---\nx".toList h
    have hOffset : 0 + listByteSize "---\nx".toList = content.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega


set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
lemma corr_end : ScannerSurfCorr endPrep endPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"---\nx\n".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "---\nx\n".toList ++ endPos.chars := by cbv
    rw [hSplit] at h
    have ht := chars_drop input "---\nx\n".toList h
    have hOffset : 0 + listByteSize "---\nx\n".toList = endPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega


set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
lemma corr_dir : ScannerSurfCorr dirPrep dirPos := by
  refine ⟨?_, (by cbv), (by cbv), ⟨"---\nx\n...\n".toList, (by cbv), by cbv⟩, ?_⟩
  · have h := chars_from_zero_toList input
    have hSplit : input.toList = "---\nx\n...\n".toList ++ dirPos.chars := by cbv
    rw [hSplit] at h
    have ht := chars_drop input "---\nx\n...\n".toList h
    have hOffset : 0 + listByteSize "---\nx\n...\n".toList = dirPrep.offset := by cbv
    rw [hOffset] at ht
    exact ht
  · intro i hi hpos
    change i < 1 at hi
    omega


set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
/-- Actual seed → `---` → scalar → `...` → directive. Every reachability
edge is the executable scanNextToken, and the annotated stream is constructed
through the new producer and its native consumer, with no route hypothesis. -/
lemma native_directive_after_explicit_scalar :
    ScannerReachable input directed ∧
    ∃ stop, ScannerSurfCorr directed stop ∧
      TSLYamlStream start directed dirPos [.beginDocument, .endDocument] []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirPos stop)).toList ∧
      TPendingNode start true dirPos stop [.beginDocument, .endDocument] []
        (L4YAML.Proofs.Serialization.EventsOf.declaredHandle (span dirPos stop)).toList ∧
      DirectiveRoute start dirPos [.beginDocument, .endDocument] := by
  have hr0 : ScannerReachable input seed := .seed
  have hr1 : ScannerReachable input started := .step hr0 step_started
  have hr2 : ScannerReachable input content := .step hr1 step_content
  have hr3 : ScannerReachable input ended := .step hr2 step_ended
  have hr4 : ScannerReachable input directed := .step hr3 step_directed
  refine ⟨hr4, ?_⟩
  have hSeed : TSLYamlStream start seed start [] [] [] :=
    TSLYamlStream.seed input.toList seed (seed_tokens_only_streamStart input)
  have hInitial : TSLYamlStream start markerPrep start [] [] [] :=
    ⟨hSeed.stream, by
      rw [TPendingNode.preprocess_goOut pre_marker []]
      exact hSeed.events⟩
  obtain ⟨landing, hArm⟩ := L4YAML.Proofs.StreamAccum.contentArm_of_dispatch
    nodePrep nodePos 'x' corr_node (by cbv) (by intro _; cbv)
    (by
      intro h
      have hz : nodePrep.flowLevel = 0 := by cbv
      rw [hz] at h
      omega)
    dispatch_content
  have hLanding : landing = contentPos := by
    have hCorr : ScannerSurfCorr content landing := by cases hArm <;> assumption
    exact ScannerSurfCorr_unique hCorr corr_content
  subst landing
  have hSep : SSeparateLines 0 node nodePos :=
    .commented 0 _ _ _
      (.withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _))
      (.mk 0 _ _ _ (.zero _) (.none _))
  obtain ⟨en, hContent, hPending⟩ := content_after_docStart
    (start := start) (block := start) (marker := start) (node := node)
    (prepPos := nodePos) (landing := contentPos) (sc := markerPrep)
    (prep := nodePrep) (after := content) (c := 'x') (ev_c := [])
    hInitial (by cbv)
    (L4YAML.Proofs.StreamAccum.sslComments_refl_of_col0 (by cbv)) corr_marker
    "\nx\n...\n%YAML 1.2\n---\ny".toList (by cbv) (by cbv) (SCDirectivesEnd.mk _)
    pre_node
    hSep hArm corr_node corr_content (by cbv) (by cbv)
    dispatch_content
  have hEmpty : en = [] := by
    have he := hContent.events
    have hn : goOut content.tokens.toList [] = ([.beginDocument], []) := by cbv
    rw [hn] at he
    simpa using he
  subst en
  obtain ⟨stop, hc, ht, hp⟩ := directive_after_pending_document
    (start := start) (block := start) (scan := contentPos)
    (endLanding := endPos) (dirLanding := dirPos)
    (sc := content) (endPrep := endPrep) (ended := ended)
    (dirPrep := dirPrep) (directed := directed) (c := '.')
    (ev_c := []) (ev_o := [.beginDocument]) hContent hPending
    pre_end
    (.withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _))
    corr_end "\n%YAML 1.2\n---\ny".toList (by cbv) (by cbv)
    dispatch_end
    pre_dir
    (.withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _))
    (by cbv) corr_dir (by cbv) dispatch_dir
  have hRoute : DirectiveRoute start dirPos [.beginDocument, .endDocument] := by
    cases hp with
    | pendingDirective _ _ _ _ hr _ => exact hr
  exact ⟨stop, hc, ht, hp, hRoute⟩

#print axioms L4YAML.Tests.Guards.RightWallContentNative.native_directive_after_explicit_scalar
#print axioms L4YAML.Proofs.Serialization.TraceOf.StreamBridge.TPendingNode.content_step_noPending
#print axioms L4YAML.Proofs.Serialization.TraceOf.RightWallContent.content_step_routed0
#print axioms L4YAML.Proofs.Serialization.TraceOf.RightWallContent.content_after_docStart
#print axioms L4YAML.Proofs.Serialization.TraceOf.RightWallContent.directive_after_pending_document

end L4YAML.Tests.Guards.RightWallContentNative
end Blanket
