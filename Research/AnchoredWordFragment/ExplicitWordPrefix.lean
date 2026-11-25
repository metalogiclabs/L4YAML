module
public import Tests.Guards.Proofs.ExplicitWordExecution
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ExplicitWordPrefix
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance L4YAML.Proofs.ScalarProduction
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.ExplicitWordExecution
open L4YAML.Tests.Guards.RootInhabited
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

-- Blueprint 7.7: initialized explicit word key → native matched-colon state.
-- The suffix is completely arbitrary. The parent's Letter premise there was
-- used only to price its byte length; no suffix grammar premise is needed.
lemma source_size (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 (source k v).utf8ByteSize = 5+k.length+listByteSize v := by
 simp only [utf8ByteSize_eq_listByteSize,source,String.toList_ofList,listByteSize,listByteSize_append,
  word_bytes k hk,question_byte,space_byte,lf_byte,colon_byte]; omega

lemma initial_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanNextToken_preprocess (initial k v) = .ok (some (qpre k v,'?')) := by
 have h0 := source_zero k v
 have hs := source_size k v hk
 have hm : 0 < 5+k.length+(listByteSize v) := by omega
 have hp : (initial k v).peek? = some '?' := by
  simp [initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,hs,h0,hm]
 have hsk := skip_content_stop (initial k v) hp (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [scanNextToken_preprocess,hsk]
 simp [initial,qpre,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,
  ScannerState.currentPos,ScannerState.hasMore,ScannerState.peek?,hs,h0,hm,
  ScannerState.inFlow,ScannerState.currentIndent,
  unwindIndents,unwindIndentsLoop,saveSimpleKey,closeStaleExplicitKey,
  bind,Except.bind,pure,Pure.pure,Except.pure,pos,tok]

lemma question_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanKey (qstart k v) = .ok (qout k v) := by
 have h0 := source_zero k v
 have h1 := source_one k v
 have hs := source_size k v hk
 have hm0 : 0 < 5+k.length+(listByteSize v) := by omega
 have hm1 : 1 < 5+k.length+(listByteSize v) := by omega
 simp [scanKey,scanKeyValidate,qstart,qpre,qout,initial,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.inFlow,ScannerState.currentIndent,ScannerState.peek?,ScannerState.advance,
  ScannerState.hasTabInPrecedingWhitespace,ScannerState.hasTabInPrecedingWhitespaceLoop,
  ScannerState.markerOnLine,lastTokenIsNodePropertyOnLine,lastRealToken?,YamlToken.isNodeProperty,atSequenceIndent,
  pushMappingIndent,String.Pos.Raw.next,next_byteIdx,hs,h0,h1,hm0,hm1,
  bind,Except.bind,pure,Pure.pure,Except.pure,pos,tok]

lemma key_preprocess (c : Char) (ks v : List Char)
 (hk : ∀ d ∈ c::ks, Letter d) :
 scanNextToken_preprocess (qout (c::ks) v) = .ok (some (kpre (c::ks) v,c)) := by
 have h1 := source_one (c::ks) v
 have h2 := source_key c ks v
 have hs := source_size (c::ks) v hk
 have hm1 : 1 < 5+(c::ks).length+(listByteSize v) := by omega
 have hm2 : 2 < 5+(c::ks).length+(listByteSize v) := by omega
 simp only [List.length_cons] at hs hm1 hm2
 have hp : (qout (c::ks) v).peek? = some ' ' := by
  simp [qout,qstart,qpre,initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,hs,h1,hm1]
 have had := advance_unit hp (by decide) (by decide) (by decide)
 have ha : (qout (c::ks) v).advance.peek? = some c := by
  rw [had]
  simp [shift,qout,qstart,qpre,initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,hs,h2,hm2]
 have hf := letter_facts (hk c (by simp))
 have hwhite := hf.2.2.2.2.2.2.2.2.2
 simp only [Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hwhite
 have hsk := skip_one_space (qout (c::ks) v) hp ha (by rfl) hwhite.1 hwhite.2 hf.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1
 rw [scanNextToken_preprocess,hsk,had]
 simp [shift,qout,qstart,qpre,kpre,initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,
  ScannerState.currentPos,ScannerState.hasMore,ScannerState.peek?,hs,h2,hm2,
  ScannerState.inFlow,saveSimpleKey,closeStaleExplicitKey,PendingKeys.staleGate,
  bind,Except.bind,pure,Pure.pure,Except.pure,pos,tok]

lemma colon_skip (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 skipToContent (kout k v) = .ok (newlineState k v) := by
 have h2 := source_lf k v hk
 have h3 := source_colon k v hk
 have hs := source_size k v hk
 have hm2 : 2+k.length < 5+k.length+(listByteSize v) := by omega
 have hm3 : 3+k.length < 5+k.length+(listByteSize v) := by omega
 have hp : (kout k v).peek? = some '\n' := by
  simp [kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,
   ScannerState.emitAt,ScannerState.peek?,hs,h2,hm2]
 have hget : String.Pos.Raw.get (kout k v).input ⟨(kout k v).offset⟩ = '\n' := by
  simpa [ScannerState.peek?,show (kout k v).offset<(kout k v).inputEnd by
   simpa [kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,
    ScannerState.emitAt,hs] using hm2] using hp
 have hnl : {consumeNewline (kout k v) with simpleKeyAllowed:=true} = newlineState k v := by
  rw [consumeNewline,hp,advance_lf hp]
  simp [newlineState,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,
   ScannerState.emitAt,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have hup : (newlineState k v).peek? = some ':' := by
  simp [newlineState,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,
   ScannerState.emitAt,ScannerState.peek?,hs,h3,hm3]
 have hstop := skip_content_loop_stop (newlineState k v) hup (by decide) (by decide) (by decide) (by decide) (by decide)
 have hws : skipToContentWs (kout k v) = .ok (kout k v) := by
  have hw : skipWhitespace (kout k v) = kout k v :=
   skip_whitespace_stop (kout k v) hp (by decide) _
  simp [skipToContentWs,show (kout k v).needIndentCheck=false by rfl,hw]
 have hcomm : skipToContentComment (kout k v) = kout k v := by simp [skipToContentComment,hp]
 unfold skipToContent
 rw [skipToContentLoop]
 simp only [hws,Except.bind,hcomm,hp]
 change (if !(consumeNewline (kout k v)).inFlow then
   skipToContentLoop {consumeNewline (kout k v) with simpleKeyAllowed:=true}
    ((kout k v).inputEnd-(kout k v).offset)
  else skipToContentLoop (consumeNewline (kout k v))
    ((kout k v).inputEnd-(kout k v).offset)) = _
 have hfl : (consumeNewline (kout k v)).inFlow=false := by
  have := congrArg ScannerState.inFlow hnl
  simpa [ScannerState.inFlow,newlineState,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
   ScannerState.mk',ScannerState.emit,ScannerState.emitAt] using this
 rw [hfl]; simp only [Bool.not_false,ite_true,hnl]; exact hstop _

lemma colon_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanNextToken_preprocess (kout k v) = .ok (some (cpre k v,':')) := by
 have hsk := colon_skip k v hk
 have h3 := source_colon k v hk
 have h4 := source_space k v hk
 have hs := source_size k v hk
 have hm3 : 3+k.length < 5+k.length+(listByteSize v) := by omega
 have hm4 : 4+k.length < 5+k.length+(listByteSize v) := by omega
 simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hm3 hm4 h3 h4
 rw [scanNextToken_preprocess,hsk]
 simp [newlineState,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.hasMore,ScannerState.peek?,ScannerState.peekAt?,ScannerState.peekAt?Loop,
  ScannerState.inFlow,ScannerState.currentIndent,unwindIndents,unwindIndentsLoop,
  saveSimpleKey,closeStaleExplicitKey,PendingKeys.staleGate,PendingKeys.indicatorAt,
  String.Pos.Raw.next,String.Pos.Raw.add_char_eq,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,isLineBreakBool,isLineFeedBool,isCarriageReturnBool,hs,h3,h4,hm3,hm4,pos,tok,
  bind,Except.bind,pure,Pure.pure,Except.pure,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma colon_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanValue (cpre k v) = .ok (cout k v) := by
 have h2 := source_lf k v hk
 have h3 := source_colon k v hk
 have h4 := source_space k v hk
 have hprev := source_prev_colon k v hk
 have hs := source_size k v hk
 have hm3 : 3+k.length < 5+k.length+(listByteSize v) := by omega
 have hm4 : 4+k.length < 5+k.length+(listByteSize v) := by omega
 have hclose : PendingKeys.close #[-1,0] #[none,some 0] 0 = (#[none,none],none,-1) := by
  have hr0 : Array.range 0 = #[] := Array.range_eq_empty_iff.mpr rfl
  have hr : Array.range 2 = #[0,1] := by simp [Array.range_succ,hr0]
  have hc : PendingKeys.closeAt #[-1,0] #[none,some 0] 0 = #[none,none] := by
   simp [PendingKeys.closeAt,hr]
  simp only [PendingKeys.close,hc,PendingKeys.innermost]
  simp only [show (#[none,none] : Array (Option Nat)).size = 2 from rfl, hr]
  simp [Array.findSomeRev?_push]
 simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hm3 hm4 h2 h3 h4 hprev
 simp [scanValue,scanValueClearKey,scanValueValidate,scanValueIndentTabCheck,scanValuePrepare,
  scanValueTabCheck,scanValueKeySurvives,flowGluedCollectionValue,
  cpre,cout,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.inFlow,ScannerState.currentIndent,ScannerState.markerOnLine,ScannerState.indentColumns,
  ScannerState.hasTabInPrecedingWhitespace,ScannerState.hasTabInPrecedingWhitespaceLoop,
  ScannerState.tabInLineIndent,ScannerState.tabInLineIndentLoop,
  ScannerState.advance,ScannerState.peek?,String.Pos.Raw.next,String.Pos.Raw.add_char_eq,
  h2,h3,h4,hprev,hs,hm3,hm4,hclose,pos,tok,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma common_question (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 Common (initial k v) (qpre k v) '?' := by
 have h0 := source_zero k v
 have hs := source_size k v hk
 have hm : 0<5+k.length+(listByteSize v) := by omega
 simp [Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,h0,hs,hm]

lemma common_colon (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 Common (kout k v) (cpre k v) ':' := by
 have h3 := source_colon k v hk
 have hs := source_size k v hk
 have hm : 3+k.length<5+k.length+(listByteSize v) := by omega
 simp [Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,h3,hs,hm]

lemma question_flag (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 (isKeyCandidate (qstart k v) && flowKeyPredecessorOk (qstart k v) && flowKeyFollowerOk (qstart k v)) = true := by
 have h0 := source_zero k v
 have h1 := source_one k v
 have hs := source_size k v hk
 have hm0 : 0<5+k.length+(listByteSize v) := by omega
 have hm1 : 1<5+k.length+(listByteSize v) := by omega
 simp [isKeyCandidate,flowKeyPredecessorOk,flowKeyFollowerOk,qstart,qpre,initial,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.inFlow,
  ScannerState.peekAt?,ScannerState.peekAt?Loop,String.Pos.Raw.next,String.Pos.Raw.add_char_eq,
  hs,h0,h1,hm0,hm1,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool]

lemma colon_flag (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 isValueCandidate (cpre k v) = true := by
 have h3 := source_colon k v hk
 have h4 := source_space k v hk
 have hs := source_size k v hk
 have hm3 : 3+k.length<5+k.length+(listByteSize v) := by omega
 have hm4 : 4+k.length<5+k.length+(listByteSize v) := by omega
 simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hm3 hm4 h3 h4
 simp [isValueCandidate,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.inFlow,
  ScannerState.peekAt?,ScannerState.peekAt?Loop,String.Pos.Raw.next,String.Pos.Raw.add_char_eq,
  hs,h3,h4,hm3,hm4,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,
  Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma question_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanNextToken (initial k v) = .ok (some (qout k v)) := by
 apply stepBlock (initial_preprocess k v hk) (common_question k v hk)
 rw [upd_q]
 simp [scanNextToken_dispatchBlockIndicators,question_flag k v hk,question_scan k v hk,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma key_step (c : Char) (ks v : List Char)
 (hk : ∀ d ∈ c::ks, Letter d) :
 scanNextToken (qout (c::ks) v) = .ok (some (kout (c::ks) v)) := by
 have hc := hk c (by simp)
 have hb := letter_block (kpre (c::ks) v) c hc
 apply stepContent (key_preprocess c ks v hk) (common_key (c::ks) v c hc)
 · rw [upd_k,hb.1]; rfl
 · rw [upd_k,hb.2.1]; rfl
 · rw [upd_k,letter_dispatch _ _ hc]; exact key_scan _ _ hk

lemma colon_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanNextToken (kout k v) = .ok (some (cout k v)) := by
 apply stepBlock (colon_preprocess k v hk) (common_colon k v hk)
 rw [upd_c]
 simp [scanNextToken_dispatchBlockIndicators,colon_flag k v hk,colon_scan k v hk,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma initial_peek (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 (initial k v).peek? = some '?' := by
 have hs := source_size k v hk
 have hm : 0<5+k.length+(listByteSize v) := by omega
 simp [initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,hs,source_zero k v,hm]

#print axioms question_step
#print axioms key_step
#print axioms colon_step
end L4YAML.Tests.Guards.ExplicitWordPrefix

