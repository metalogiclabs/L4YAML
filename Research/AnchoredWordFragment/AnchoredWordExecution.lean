module
public import Tests.Guards.Proofs.ExplicitWordPrefix
public import Tests.Guards.Proofs.AnchoredWordSource
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredWordExecution
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance L4YAML.Proofs.ScalarProduction
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.ExplicitWordExecution
open L4YAML.Tests.Guards.RootInhabited
open L4YAML.Tests.Guards.AnchoredWordSource
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

-- Capstone path: Blueprint 7.7; the actual initialized five-step scanner fold.
def anchorPre (k v : List Char) : ScannerState := vpre k (suffix v)
def anchorScanOut (k v : List Char) : ScannerState :=
 {(shift (anchorPre k v) 2).emitAt (anchorPre k v).currentPos (.anchor "a") with simpleKeyAllowed:=false}
def anchorOut (k v : List Char) : ScannerState :=
 {anchorScanOut k v with definedAnchors:=(anchorScanOut k v).definedAnchors.push "a"}
def scalarPre (k v : List Char) : ScannerState := shift (anchorOut k v) 1
def scalarOut (k v : List Char) : ScannerState := afterWord (scalarPre k v) v

lemma source_size (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (AnchoredWordSource.source k v).utf8ByteSize = 8+k.length+v.length := by
 rw [AnchoredWordSource.source,ExplicitWordPrefix.source_size k (suffix v) hk,suffix_bytes v hv]
 omega

lemma anchor_corr (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 ScannerSurfCorr (anchorPre k v) ⟨'&'::'a'::' '::v,2⟩ := value_corr k (suffix v) hk

lemma unit_corr {s : ScannerState} {c : Char} {tail : List Char}
 (hc : ScannerSurfCorr s ⟨c::tail,s.col⟩) (hn : c≠'\n') (hr : c≠'\r') (hu : c.utf8Size=1) :
 ScannerSurfCorr (shift s 1) ⟨tail,s.col+1⟩ := by
 have hp := corr_peek_head hc
 have ha := advance_unit hp hn hr hu
 simpa [ha,shift] using advance_non_newline_corr s c tail hc (peek_some_has_more hp) hn hr

lemma anchor_loop (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 collectAnchorNameLoop (anchorPre k v).advance "" ((anchorPre k v).inputEnd-(anchorPre k v).advance.offset) =
 ("a",shift (anchorPre k v) 2) := by
 have hc : ScannerSurfCorr (anchorPre k v) ⟨'&'::'a'::' '::v,(anchorPre k v).col⟩ := anchor_corr k v hk
 have hp := corr_peek_head hc
 have hca : ScannerSurfCorr (shift (anchorPre k v) 1) ⟨'a'::' '::v,3⟩ :=
  unit_corr hc (by decide) (by decide) (by decide)
 have hpa := corr_peek_head hca
 have hcs : ScannerSurfCorr (shift (anchorPre k v) 2) ⟨' '::v,4⟩ := by
  have h := unit_corr hca (by decide) (by decide) (by decide)
  change ScannerSurfCorr (shift (shift (anchorPre k v) 1) 1) ⟨' '::v,4⟩ at h
  simpa only [shift_add] using h
 have hps := corr_peek_head hcs
 have ha0 := advance_unit hp (by decide) (by decide) (by decide)
 have ha1 := advance_unit hpa (by decide) (by decide) (by decide)
 have hf := peek_some_has_more hps
 have hle : 2 ≤ (anchorPre k v).inputEnd - (shift (anchorPre k v) 1).offset := by
  simp only [shift] at hf ⊢; omega
 obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hle
 have he : (anchorPre k v).inputEnd - (shift (anchorPre k v) 1).offset = (n+1)+1 := by omega
 have hcondA : (!isFlowIndicatorBool 'a' && !isWhiteSpaceBool 'a' && !isLineBreakBool 'a'
   && isPrintableBool 'a' && 'a' != '\uFEFF') = true := by decide
 have hcondS : (!isFlowIndicatorBool ' ' && !isWhiteSpaceBool ' ' && !isLineBreakBool ' '
   && isPrintableBool ' ' && ' ' != '\uFEFF') = false := by decide
 rw [ha0,he]
 simp [collectAnchorNameLoop,hpa,ha1,shift_add,hps,
  isFlowIndicatorBool,isWhiteSpaceBool,isSpaceBool,isTabBool,isLineBreakBool,isLineFeedBool,isCarriageReturnBool,
  isPrintableBool,isPrintableProp]

lemma anchor_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanAnchorOrAlias (anchorPre k v) true = .ok (anchorScanOut k v) := by
 simp only [scanAnchorOrAlias]
 simp only [anchor_loop k v hk]
 simp [anchorScanOut]

lemma anchor_dispatch (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanNextToken_dispatchContent (anchorPre k v) '&' = .ok (anchorOut k v) := by
 have hc : ScannerSurfCorr (anchorPre k v) ⟨'&'::'a'::' '::v,(anchorPre k v).col⟩ := anchor_corr k v hk
 have hca : ScannerSurfCorr (shift (anchorPre k v) 1) ⟨'a'::' '::v,3⟩ :=
  unit_corr hc (by decide) (by decide) (by decide)
 have hcs : ScannerSurfCorr (shift (anchorPre k v) 2) ⟨' '::v,4⟩ := by
  have h := unit_corr hca (by decide) (by decide) (by decide)
  change ScannerSurfCorr (shift (shift (anchorPre k v) 1) 1) ⟨' '::v,4⟩ at h
  simpa only [shift_add] using h
 have hs : propertyFollowerOk (anchorNameEnd (anchorPre k v))=true := by
  simp [anchorNameEnd,anchor_loop k v hk,propertyFollowerOk,corr_peek_head hcs,isWhiteSpaceBool,isSpaceBool,isTabBool]
 have hg : propertyRunHasAnchor (anchorPre k v)=false ∧ propertyRunFull (anchorPre k v)=false := by
  simp [propertyRunHasAnchor,propertyRunFull,trailingPropertyRun,trailingPropertyRunOnLine,YamlToken.isAnchorProperty,
  YamlToken.isNodeProperty,ScannerState.inFlow,
  anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
  afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,
  lastRealTokenVal?,lastRealTokenIdx?,lastRealToken?,prevRealIdx?,pos,ExplicitWordExecution.tok,
  bind,Except.bind,pure,Pure.pure,Except.pure]
 simp [scanNextToken_dispatchContent,hg.1,hg.2,hs,anchor_scan k v hk,anchor_loop k v hk,
  anchorOut,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma preprocess_from_skip {s t u : ScannerState} {c : Char}
 (hskip : skipToContent s=.ok t) (hmore : t.hasMore=true) (hneed : t.needIndentCheck=false)
 (hclose : closeStaleExplicitKey (saveSimpleKey t)=u) (hpeek : u.peek?=some c) :
 scanNextToken_preprocess s=.ok (some (u,c)) := by
 simp [scanNextToken_preprocess,hskip,hmore,hneed,hclose,hpeek,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma anchor_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanNextToken_preprocess (cout k (suffix v))=.ok (some (anchorPre k v,'&')) := by
 have ha := corr_peek_head (anchor_corr k v hk)
 have h4 := source_space k (suffix v) hk
 have hs := ExplicitWordPrefix.source_size k (suffix v) hk
 have hm4 : 4+k.length<5+k.length+listByteSize (suffix v) := by omega
 have hp : (cout k (suffix v)).peek?=some ' ' := by
  simp [cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,
   ScannerState.emitAt,ScannerState.peek?,hs,h4,hm4]
 have had := advance_unit hp (by decide) (by decide) (by decide)
 have hh : (shift (cout k (suffix v)) 1).peek?=(anchorPre k v).peek? := by
  simp [ScannerState.peek?,shift,anchorPre,vpre,cout,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have haa : (cout k (suffix v)).advance.peek?=some '&' := by rw [had,hh]; exact ha
 have hsk := skip_one_space (cout k (suffix v)) hp haa (by rfl)
  (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [had] at hsk
 have hm : (shift (cout k (suffix v)) 1).hasMore=true := by
  simp only [ScannerState.hasMore]; exact decide_eq_true (peek_some_has_more (hh.trans ha))
 have hcl : closeStaleExplicitKey (saveSimpleKey (shift (cout k (suffix v)) 1))=anchorPre k v := by
  simp [saveSimpleKey,closeStaleExplicitKey,PendingKeys.staleGate,shift,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
   afterWord,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,ScannerState.inFlow,
   pos,ExplicitWordExecution.tok,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 exact preprocess_from_skip hsk hm (by rfl) hcl ha

lemma scalar_corr (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 ScannerSurfCorr (scalarPre k v) ⟨v,5⟩ := by
 apply corr_at_prefix (scalarPre k v) (['?',' ']++k++['\n',':',' ','&','a',' '])
 · simp [scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
    ScannerState.mk',ExplicitWordFragment.source,afterWord,shift,ScannerState.emit,ScannerState.emitAt,suffix]
 · rfl
 · simp [scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,shift,ScannerState.emitAt,listByteSize_append,listByteSize,
    word_bytes k hk,show '&'.utf8Size=1 from by decide,show 'a'.utf8Size=1 from by decide,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 · intro i hi hp
   simp [scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,afterWord,shift,ScannerState.emitAt] at hi ⊢
   have : i=1 := by omega
   subst i; simp

lemma scalar_preprocess (k : List Char) (d : Char) (vs : List Char)
 (hk : ∀ c ∈ k, Letter c) (hd : Letter d) :
 scanNextToken_preprocess (anchorOut k (d::vs))=.ok (some (scalarPre k (d::vs),d)) := by
 have hc := scalar_corr k (d::vs) hk
 have hpa : (scalarPre k (d::vs)).peek?=some d := corr_peek_head hc
 have hps : (anchorOut k (d::vs)).peek?=some ' ' := by
  have hco : ScannerSurfCorr (anchorOut k (d::vs)) ⟨' '::d::vs,4⟩ := by
   apply corr_at_prefix (anchorOut k (d::vs)) (['?',' ']++k++['\n',':',' ','&','a'])
   · simp [anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
      ScannerState.mk',ExplicitWordFragment.source,afterWord,shift,ScannerState.emit,ScannerState.emitAt,suffix]
   · rfl
   · simp [anchorOut,anchorScanOut,anchorPre,vpre,shift,ScannerState.emitAt,listByteSize_append,listByteSize,
      word_bytes k hk,show '&'.utf8Size=1 from by decide,show 'a'.utf8Size=1 from by decide,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
   · intro i hi hp
     simp [anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,afterWord,shift,ScannerState.emitAt] at hi ⊢
     have : i=1 := by omega
     subst i; simp
  exact corr_peek_head hco
 have had := advance_unit hps (by decide) (by decide) (by decide)
 have haa : (anchorOut k (d::vs)).advance.peek?=some d := by rw [had]; exact hpa
 have hf := letter_facts hd
 have hwhite := hf.2.2.2.2.2.2.2.2.2
 simp only [Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hwhite
 have hsk := skip_one_space (anchorOut k (d::vs)) hps haa (by rfl)
  hwhite.1 hwhite.2 hf.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1
 rw [had] at hsk
 have hm : (scalarPre k (d::vs)).hasMore=true := by
  simp only [ScannerState.hasMore]; exact decide_eq_true (peek_some_has_more hpa)
 have hcl : closeStaleExplicitKey (saveSimpleKey (scalarPre k (d::vs)))=scalarPre k (d::vs) := by
  simp [saveSimpleKey,closeStaleExplicitKey,PendingKeys.staleGate,scalarPre,anchorOut,anchorScanOut,anchorPre,
   vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',
   ScannerState.emit,ScannerState.emitAt,ScannerState.inFlow]
 exact preprocess_from_skip hsk hm (by rfl) hcl hpa

lemma scalar_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanPlainScalar (scalarPre k v) = .ok (scalarOut k v) :=
 word_eof v (scalarPre k v) hv (scalar_corr k v hk) (by simp [scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,shift,ScannerState.emitAt]) (by rfl)

lemma common_anchor (k v : List Char) :
 Common (cout k (suffix v)) (anchorPre k v) '&' := by
 simp [anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma common_scalar (k v : List Char) (c : Char) (hc : Letter c) :
 Common (anchorOut k v) (scalarPre k v) c := by
 have hi := (letter_facts hc).2.2.2.2.2.2.2.2.1
 simp only [isIndicatorBool,decide_eq_false_iff_not,List.mem_cons,List.mem_singleton,not_or] at hi
 simp_all [anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma anchor_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanNextToken (cout k (suffix v)) = .ok (some (anchorOut k v)) := by
 apply stepContent (anchor_preprocess k v hk) (common_anchor k v)
 · simp [upd,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,afterWord,shift,ScannerState.emitAt,
    scanNextToken_dispatchBlockIndicators,noneGood,pure,Except.pure]
 · simp [upd,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,afterWord,shift,ScannerState.emitAt,
    scanNextToken_checkAdjacentValue,Except.isOk,Except.toBool]
 · have hu : upd (anchorPre k v)=anchorPre k v := upd_v k (suffix v)
   rw [hu]
   exact anchor_dispatch k v hk

lemma scalar_step (k : List Char) (d : Char) (vs : List Char)
 (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ d::vs, Letter c) :
 scanNextToken (anchorOut k (d::vs)) = .ok (some (scalarOut k (d::vs))) := by
 have hd := hv d (by simp)
 have hb := letter_block (scalarPre k (d::vs)) d hd
 have hu : upd (scalarPre k (d::vs))=scalarPre k (d::vs) := by
  simp [upd,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,afterWord,shift,ScannerState.emitAt]
 apply stepContent (scalar_preprocess k d vs hk hd) (common_scalar k (d::vs) d hd)
 · rw [hu,hb.1]; rfl
 · rw [hu,hb.2.1]; rfl
 · rw [hu,letter_dispatch _ _ hd]; exact scalar_scan _ _ hk hv

lemma scalar_eof (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (scalarOut k v).offset=(AnchoredWordSource.source k v).utf8ByteSize ∧
 scanNextToken (scalarOut k v)=.ok none := by
 have hs := source_size k v hk hv
 have hoff : (scalarOut k v).offset=(AnchoredWordSource.source k v).utf8ByteSize := by
  simp [scalarOut,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,afterWord,shift,ScannerState.emitAt,hs,Nat.add_assoc]; omega
 refine ⟨hoff,?_⟩
 have he : (scalarOut k v).inputEnd ≤ (scalarOut k v).offset := by
  rw [hoff]; exact Nat.le_refl _
 have hp := preprocess_eof (scalarOut k v) he (by rfl)
 simp [scanNextToken,hp,bind,Except.bind,pure,Pure.pure,Except.pure]

def finalTokens (k v : List Char) : Array (Positioned YamlToken) :=
 ((unwindIndents (scalarOut k v) (-1)).emit .streamEnd).tokens
def filteredTokens (k v : List Char) : Array (Positioned YamlToken) :=
 (finalTokens k v).filter (fun t => t.val != .placeholder)

lemma final_checks (k v : List Char) :
 scanLoop_checkDanglingNode (scalarOut k v)=.ok () ∧
 scanLoop_checkFlowValueIndent (scalarOut k v)=.ok () := by
 simp [anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,scanLoop_checkDanglingNode,scanLoop_checkFlowValueIndent,danglingNodePos?,underIndentedFlowValuePos?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,ScannerState.inFlow,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma final_loop (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) (n : Nat) :
 scanLoop (scalarOut k v) (n+1)=.ok (finalTokens k v) := by
 rw [scanLoop,(scalar_eof k v hk hv).2]
 have hc := final_checks k v
 simp only [show (scalarOut k v).flowLevel=0 from rfl,show (scalarOut k v).directivesPresent=false from rfl]
 simp [hc.1,hc.2,finalTokens]

def expectedTokens (k v : List Char) : Array (Positioned YamlToken) :=
 #[ExplicitWordExecution.tok (pos 0 0 0) .streamStart,ExplicitWordExecution.tok (pos 0 0 0) .blockMappingStart,
  ExplicitWordExecution.tok (pos 0 0 0) .key,
  ExplicitWordExecution.tok (pos 2 0 2) (.scalar (String.ofList k) .plain),
  ExplicitWordExecution.tok (pos (3+k.length) 1 0) .value,
  ExplicitWordExecution.tok (pos (5+k.length) 1 2) (.anchor "a"),
  ExplicitWordExecution.tok (pos (8+k.length) 1 5) (.scalar (String.ofList v) .plain),
  ExplicitWordExecution.tok (pos (8+k.length+v.length) 1 (5+v.length)) .blockEnd,
  ExplicitWordExecution.tok (pos (8+k.length+v.length) 1 (5+v.length)) .streamEnd]

lemma filtered_shape (k v : List Char) : filteredTokens k v=expectedTokens k v := by
 simp [filteredTokens,finalTokens,expectedTokens,unwindIndents,unwindIndentsLoop,
  ScannerState.currentIndent,scalarOut,scalarPre,anchorOut,anchorScanOut,anchorPre,vout,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,ExplicitWordExecution.tok,
  Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma anchored_word_fold (k v : List Char) (hk : Word k) (hv : Word v) (n : Nat) :
 scanLoop (initial k (suffix v)) (n+5)=scanLoop (scalarOut k v) n := by
 cases k with
 | nil => exact False.elim (hk.1 rfl)
 | cons c ks =>
  cases v with
  | nil => exact False.elim (hv.1 rfl)
  | cons d vs =>
   calc
    _ = scanLoop (qout (c::ks) (suffix (d::vs))) (n+4) := by rw [scanLoop,ExplicitWordPrefix.question_step _ _ hk.2]
    _ = scanLoop (kout (c::ks) (suffix (d::vs))) (n+3) := by rw [scanLoop,ExplicitWordPrefix.key_step c ks _ hk.2]
    _ = scanLoop (cout (c::ks) (suffix (d::vs))) (n+2) := by rw [scanLoop,ExplicitWordPrefix.colon_step _ _ hk.2]
    _ = scanLoop (anchorOut (c::ks) (d::vs)) (n+1) := by rw [scanLoop,anchor_step _ _ hk.2]
    _ = scanLoop (scalarOut (c::ks) (d::vs)) n := by rw [scanLoop,scalar_step _ d vs hk.2 hv.2]

lemma anchored_word_filtered (k v : List Char) (hk : Word k) (hv : Word v) :
 scanFiltered (AnchoredWordSource.source k v)=.ok (expectedTokens k v) := by
 have hs := source_size k v hk.2 hv.2
 have hp := ExplicitWordPrefix.initial_peek k (suffix v) hk.2
 have hbound : 6 ≤ ((AnchoredWordSource.source k v).utf8ByteSize+1)*4 := by rw [hs]; omega
 obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hbound
 have hfuel : ((AnchoredWordSource.source k v).utf8ByteSize+1)*4=(n+1)+5 := by omega
 have hscan : scan (AnchoredWordSource.source k v)=.ok (finalTokens k v) := by
  unfold scan
  change scanLoop (match (initial k (suffix v)).peek? with
   | some '\uFEFF' => (initial k (suffix v)).consumeBOM | _ => initial k (suffix v)) _ = _
  rw [hp]
  change scanLoop (initial k (suffix v)) (((AnchoredWordSource.source k v).utf8ByteSize+1)*4) = _
  rw [hfuel,anchored_word_fold k v hk hv,final_loop k v hk.2 hv.2 n]
 simp only [scanFiltered,hscan]
 change (Except.ok (filteredTokens k v) : Except ScanError _)=.ok (expectedTokens k v)
 rw [filtered_shape]

#print axioms anchor_scan
#print axioms anchored_word_filtered
#print axioms anchored_word_fold
end L4YAML.Tests.Guards.AnchoredWordExecution

