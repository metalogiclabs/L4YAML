module
public import Tests.Guards.Proofs.AnchoredAliasStates
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredAliasExecution
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance L4YAML.Proofs.ScalarProduction
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.ExplicitWordExecution
open L4YAML.Tests.Guards.RootInhabited
open L4YAML.Tests.Guards.AnchoredWordSource (suffix)
open L4YAML.Tests.Guards.AnchoredWordExecution
open L4YAML.Tests.Guards.AnchoredAliasSource
open L4YAML.Tests.Guards.AnchoredAliasStates
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

lemma newline_skip {s t : ScannerState} {c : Char}
 (hp : s.peek?=some '\n') (hn : s.needIndentCheck=false)
 (hnl : {consumeNewline s with simpleKeyAllowed:=true}=t) (hfl : t.inFlow=false)
 (ht : t.peek?=some c) (hspace : c≠' ') (htab : c≠'\t') (hhash : c≠'#')
 (hw : isWhiteSpaceBool c=false) (hb : isLineBreakBool c=false) : skipToContent s=.ok t := by
 have hstop := skip_content_loop_stop t ht hspace htab hhash hw hb
 have hws : skipToContentWs s=.ok s := by
  have hs : skipWhitespace s=s := skip_whitespace_stop s hp (by decide) _
  simp [skipToContentWs,hn,hs]
 have hcomm : skipToContentComment s=s := by simp [skipToContentComment,hp]
 have hfl' : (consumeNewline s).inFlow=false := by
  have h := congrArg ScannerState.inFlow hnl
  change (consumeNewline s).inFlow=t.inFlow at h
  exact h.trans hfl
 unfold skipToContent
 rw [skipToContentLoop]
 simp only [hws,Except.bind,hcomm,hp]
 change (if !(consumeNewline s).inFlow then
  skipToContentLoop {consumeNewline s with simpleKeyAllowed:=true} (s.inputEnd-s.offset)
  else skipToContentLoop (consumeNewline s) (s.inputEnd-s.offset)) = _
 rw [hfl']; simp only [Bool.not_false,ite_true,hnl]
 exact hstop _

lemma q_skip (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 skipToContent (stop k v)=.ok (qline k v) := by
 have hp : (stop k v).peek?=some '\n' := corr_peek_head (stop_corr k v hk hv)
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hg := (ending_gets k v hk hv).2.1
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs hg
 have hq : (qline k v).peek?=some '?' := by
  simp [qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
   afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,tailOffset,
   hs,hg,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have hnl : {consumeNewline (stop k v) with simpleKeyAllowed:=true}=qline k v := by
  rw [consumeNewline,hp,advance_lf hp]
  simp [qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,afterWord,shift,ScannerState.emitAt,tailOffset,
   Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 exact newline_skip hp (by rfl) hnl (by rfl) hq (by decide) (by decide) (by decide) (by decide) (by decide)

lemma q_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken_preprocess (stop k v)=.ok (some (qp k v,'?')) := by
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hg := (ending_gets k v hk hv).2.1
 have hspace := (ending_gets k v hk hv).2.2.1
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs hg hspace
 rw [scanNextToken_preprocess,q_skip k v hk hv]
 simp [qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
  afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.hasMore,ScannerState.peek?,ScannerState.peekAt?,ScannerState.peekAt?Loop,
  ScannerState.inFlow,ScannerState.currentIndent,unwindIndents,unwindIndentsLoop,saveSimpleKey,closeStaleExplicitKey,
  PendingKeys.staleGate,PendingKeys.indicatorAt,String.Pos.Raw.next,String.Pos.Raw.add_char_eq,
  isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,isLineBreakBool,isLineFeedBool,isCarriageReturnBool,
  tailOffset,hs,hg,hspace,pos,tok,bind,Except.bind,pure,Pure.pure,Except.pure,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma q_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanKey (qp k v)=.ok (qo k v) := by
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hg := (ending_gets k v hk hv).2.1
 have hspace := (ending_gets k v hk hv).2.2.1
 have hprev := prev_question k v hk hv
 have hlf := (ending_gets k v hk hv).1
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs hg hspace hprev hlf
 simp [scanKey,scanKeyValidate,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
  afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,ScannerState.inFlow,
  ScannerState.currentIndent,ScannerState.peek?,ScannerState.advance,ScannerState.hasTabInPrecedingWhitespace,
  ScannerState.hasTabInPrecedingWhitespaceLoop,ScannerState.markerOnLine,lastTokenIsNodePropertyOnLine,
  lastRealToken?,YamlToken.isNodeProperty,atSequenceIndent,pushMappingIndent,String.Pos.Raw.next,next_byteIdx,
  tailOffset,hs,hg,hspace,hprev,hlf,pos,tok,bind,Except.bind,pure,Pure.pure,Except.pure,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma copy_corr (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 ScannerSurfCorr (kp k v) ⟨['c','o','p','y','\n',':',' ','*','a'],2⟩ := by
 apply corr_at_prefix (kp k v) (baseChars k v++['\n','?',' '])
 · simp [kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
    afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,AnchoredAliasSource.source,AnchoredWordSource.source,
    ExplicitWordFragment.source,suffix,body,baseChars,ending,List.append_assoc]
 · rfl
 · simp [kp,listByteSize_append,base_bytes k v hk hv,
    show listByteSize ['\n','?',' ']=3 from by decide,tailOffset]
 · intro i hi hp
   simp [kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,afterWord,shift,ScannerState.emitAt] at hi ⊢
   have : i=1 := by omega
   subst i; simp

lemma copy_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken_preprocess (qo k v)=.ok (some (kp k v,'c')) := by
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hg := (ending_gets k v hk hv).2.2.1
 have hc := corr_peek_head (copy_corr k v hk hv)
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs hg
 have hp : (qo k v).peek?=some ' ' := by
  simp [qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
   afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,tailOffset,
   hs,hg,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have had := advance_unit hp (by decide) (by decide) (by decide)
 have hha : (shift (qo k v) 1).peek?=(kp k v).peek? := by
  simp [ScannerState.peek?,shift,qo,kp,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have haa : (qo k v).advance.peek?=some 'c' := by rw [had,hha]; exact hc
 have hsk := skip_one_space (qo k v) hp haa (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [had] at hsk
 have hm : (shift (qo k v) 1).hasMore=true := by
  simp only [ScannerState.hasMore]; exact decide_eq_true (peek_some_has_more (hha.trans hc))
 have hcl : closeStaleExplicitKey (saveSimpleKey (shift (qo k v) 1))=kp k v := by
  have hsave : saveSimpleKey (shift (qo k v) 1)=kp k v := by
   simp [saveSimpleKey,shift,kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,
   vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,
   ScannerState.currentPos,ScannerState.inFlow,tailOffset,pos,tok,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  rw [hsave]
  simp only [closeStaleExplicitKey,show (kp k v).inFlow=false from rfl,Bool.false_eq_true,ite_false,
   show (kp k v).explicitKeyLine=some 2 from rfl,hc]
  simp [PendingKeys.staleGate,kp,qo,ScannerState.inFlow]
 exact preprocess_from_skip hsk hm (by rfl) hcl hc

lemma copy_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanPlainScalar (kp k v)=.ok (ko k v) := by
 apply word_before_colon ['c','o','p','y'] ['*','a'] (kp k v)
 · simp [Letter]
 · exact copy_corr k v hk hv
 · simp [kp]
 · rfl
 · rfl

lemma ko_corr (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 ScannerSurfCorr (ko k v) ⟨['\n',':',' ','*','a'],6⟩ := by
 apply corr_at_prefix (ko k v) (baseChars k v++['\n','?',' ','c','o','p','y'])
 · change (AnchoredAliasSource.source k v).toList=(baseChars k v++['\n','?',' ','c','o','p','y'])++['\n',':',' ','*','a']
   rw [source_chars]; simp [ending,List.append_assoc]
 · rfl
 · simp [ko,kp,afterWord,shift,ScannerState.emitAt,listByteSize_append,base_bytes k v hk hv,
    show listByteSize ['\n','?',' ','c','o','p','y']=7 from by decide,tailOffset,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 · intro i hi hp
   simp [ko,kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,afterWord,shift,ScannerState.emitAt] at hi ⊢
   have : i=1 := by omega
   subst i; simp

lemma c_skip (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 skipToContent (ko k v)=.ok (cline k v) := by
 have hp : (ko k v).peek?=some '\n' := corr_peek_head (ko_corr k v hk hv)
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hg := (ending_gets k v hk hv).2.2.2.2.2.1
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs hg
 have hq : (cline k v).peek?=some ':' := by
  simp [cline,ko,kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
   afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,tailOffset,
   hs,hg,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have hnl : {consumeNewline (ko k v) with simpleKeyAllowed:=true}=cline k v := by
  rw [consumeNewline,hp,advance_lf hp]
  simp [cline,ko,kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,
   afterWord,shift,ScannerState.emitAt,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 exact newline_skip hp (by rfl) hnl (by rfl) hq (by decide) (by decide) (by decide) (by decide) (by decide)

lemma c_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken_preprocess (ko k v)=.ok (some (cp k v,':')) := by
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hg := (ending_gets k v hk hv).2.2.2.2.2.1
 have hspace := (ending_gets k v hk hv).2.2.2.2.2.2.1
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs hg hspace
 rw [scanNextToken_preprocess,c_skip k v hk hv]
 simp [cp,cline,ko,kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
  afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.hasMore,ScannerState.peek?,ScannerState.peekAt?,ScannerState.peekAt?Loop,
  ScannerState.inFlow,ScannerState.currentIndent,unwindIndents,unwindIndentsLoop,saveSimpleKey,closeStaleExplicitKey,
  PendingKeys.staleGate,PendingKeys.indicatorAt,String.Pos.Raw.next,String.Pos.Raw.add_char_eq,
  isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,isLineBreakBool,isLineFeedBool,isCarriageReturnBool,
  tailOffset,hs,hg,hspace,pos,tok,bind,Except.bind,pure,Pure.pure,Except.pure,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma c_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanValue (cp k v)=.ok (co k v) := by
 rcases ending_gets k v hk hv with ⟨h0,h1,h2,h3,h7,h8,h9,h10,h11⟩
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hprev := prev_colon k v hk hv
 have hclose : PendingKeys.close #[-1,0] #[none,some 2] 0=(#[none,none],none,-1) := by
  have hr0 : Array.range 0=#[] := Array.range_eq_empty_iff.mpr rfl
  have hr : Array.range 2=#[0,1] := by simp [Array.range_succ,hr0]
  have hc : PendingKeys.closeAt #[-1,0] #[none,some 2] 0=#[none,none] := by simp [PendingKeys.closeAt,hr]
  simp only [PendingKeys.close,hc,PendingKeys.innermost]
  simp only [show (#[none,none] : Array (Option Nat)).size=2 from rfl,hr]
  simp [Array.findSomeRev?_push]
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs h7 h8 h9 hprev
 simp [scanValue,scanValueClearKey,scanValueValidate,scanValueIndentTabCheck,scanValuePrepare,
  scanValueTabCheck,scanValueKeySurvives,flowGluedCollectionValue,cp,co,cline,ko,kp,qo,qp,qline,stop,
  scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,ScannerState.inFlow,
  ScannerState.currentIndent,ScannerState.markerOnLine,ScannerState.indentColumns,
  ScannerState.hasTabInPrecedingWhitespace,ScannerState.hasTabInPrecedingWhitespaceLoop,
  ScannerState.tabInLineIndent,ScannerState.tabInLineIndentLoop,ScannerState.advance,ScannerState.peek?,
  String.Pos.Raw.next,String.Pos.Raw.add_char_eq,tailOffset,h7,h8,h9,hprev,hs,hclose,pos,tok,
  Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma alias_corr (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 ScannerSurfCorr (ap k v) ⟨['*','a'],2⟩ := by
 apply corr_at_prefix (ap k v) (baseChars k v++['\n','?',' ','c','o','p','y','\n',':',' '])
 · change (AnchoredAliasSource.source k v).toList=(baseChars k v++['\n','?',' ','c','o','p','y','\n',':',' '])++['*','a']
   rw [source_chars]; simp [ending,List.append_assoc]
 · rfl
 · simp [ap,listByteSize_append,base_bytes k v hk hv,
    show listByteSize ['\n','?',' ','c','o','p','y','\n',':',' ']=10 from by decide,tailOffset]
 · intro i hi hp
   simp [ap,co,cp,cline,ko,kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,afterWord,shift,ScannerState.emitAt] at hi ⊢
   have : i=1 := by omega
   subst i; simp

lemma alias_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken_preprocess (co k v)=.ok (some (ap k v,'*')) := by
 have hc := corr_peek_head (alias_corr k v hk hv)
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hg := (ending_gets k v hk hv).2.2.2.2.2.2.1
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs hg
 have hp : (co k v).peek?=some ' ' := by
  simp [co,cp,cline,ko,kp,qo,qp,qline,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
   afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,tailOffset,
   hs,hg,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have had := advance_unit hp (by decide) (by decide) (by decide)
 have hha : (shift (co k v) 1).peek?=(ap k v).peek? := by
  simp [ScannerState.peek?,shift,co,ap,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have haa : (co k v).advance.peek?=some '*' := by rw [had,hha]; exact hc
 have hsk := skip_one_space (co k v) hp haa (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [had] at hsk
 have hm : (shift (co k v) 1).hasMore=true := by
  simp only [ScannerState.hasMore]; exact decide_eq_true (peek_some_has_more (hha.trans hc))
 have hcl : closeStaleExplicitKey (saveSimpleKey (shift (co k v) 1))=ap k v := by
  simp [saveSimpleKey,closeStaleExplicitKey,PendingKeys.staleGate,shift,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,
   scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,
   ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,ScannerState.inFlow,
   tailOffset,pos,tok,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 exact preprocess_from_skip hsk hm (by rfl) hcl hc

lemma alias_loop (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 collectAnchorNameLoop (ap k v).advance "" ((ap k v).inputEnd-(ap k v).advance.offset)=("a",shift (ap k v) 2) := by
 have hc : ScannerSurfCorr (ap k v) ⟨['*','a'],(ap k v).col⟩ := alias_corr k v hk hv
 have hp := corr_peek_head hc
 have hca : ScannerSurfCorr (shift (ap k v) 1) ⟨['a'],3⟩ := unit_corr hc (by decide) (by decide) (by decide)
 have hpa := corr_peek_head hca
 have ha0 := advance_unit hp (by decide) (by decide) (by decide)
 have ha1 := advance_unit hpa (by decide) (by decide) (by decide)
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hf : (ap k v).inputEnd-(shift (ap k v) 1).offset=1 := by
  change (AnchoredAliasSource.source k v).utf8ByteSize-(tailOffset k v 10+1)=1
  rw [hs]; unfold tailOffset; omega
 rw [ha0,hf]
 simp [collectAnchorNameLoop,hpa,ha1,shift_add,isFlowIndicatorBool,isWhiteSpaceBool,isSpaceBool,isTabBool,
  isLineBreakBool,isLineFeedBool,isCarriageReturnBool,isPrintableBool,isPrintableProp]

lemma alias_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanAnchorOrAlias (ap k v) false=.ok (ao k v) := by
 simp only [scanAnchorOrAlias,alias_loop k v hk hv]
 simp [ao]

lemma ao_eof (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (ao k v).offset=(AnchoredAliasSource.source k v).utf8ByteSize ∧ (ao k v).peek?=none := by
 have hs := AnchoredAliasSource.source_size k v hk hv
 have hoff : (ao k v).offset=(AnchoredAliasSource.source k v).utf8ByteSize := by
  simp [ao,ap,shift,ScannerState.emitAt,tailOffset,hs]; omega
 refine ⟨hoff,?_⟩
 simp only [ScannerState.peek?,hoff,show (ao k v).inputEnd=(AnchoredAliasSource.source k v).utf8ByteSize from rfl,
  Nat.lt_irrefl,ite_false]

lemma skip_trailing_eof (s : ScannerState) (hp : s.peek?=none) (n : Nat) : skipTrailingSpaces s n=s := by
 cases n <;> simp [skipTrailingSpaces,hp]

lemma alias_close (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 validateAliasClose (ao k v)=.ok () := by
 have hp := (ao_eof k v hk hv).2
 simp [validateAliasClose,show (ao k v).inFlow=false from rfl,validateTrailingContent,
  skip_trailing_eof (ao k v) hp,hp,pure,Except.pure]

lemma alias_dispatch (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken_dispatchContent (ap k v) '*'=.ok (ao k v) := by
 have he : (shift (ap k v) 2).peek?=none := by
  have hs := AnchoredAliasSource.source_size k v hk hv
  have hge : (shift (ap k v) 2).inputEnd≤(shift (ap k v) 2).offset := by
   change (AnchoredAliasSource.source k v).utf8ByteSize≤tailOffset k v 10+2
   rw [hs]; unfold tailOffset; omega
  simp only [ScannerState.peek?,Nat.not_lt.mpr hge,ite_false]
 have hf : propertyFollowerOk (anchorNameEnd (ap k v))=true := by
  simp [anchorNameEnd,alias_loop k v hk hv,propertyFollowerOk,he]
 have hg : lastTokenIsNodeProperty (ap k v)=false := by
  have hlast : lastRealToken? (ap k v).tokens=some (tok (pos (tailOffset k v 8) 3 0) .value) := by
   simp only [ap,co]
   rw [L4YAML.Proofs.PropsRunLineCoupling.lastRealToken_push_two_ph_of_real (by rfl) (by rfl)
    (L4YAML.Proofs.FlowAdjacency.lastTokenReal_push (by simp [tok]))]
   exact L4YAML.Proofs.PropsRunLineCoupling.lastRealToken_push (by simp [tok])
  simp only [lastTokenIsNodeProperty,show (ap k v).inFlow=false from rfl,Bool.false_and,Bool.false_or,
   lastTokenIsNodePropertyOnLine,hlast]
  rfl
 have hr : (ap k v).definedAnchors=#["a"] := rfl
 simp [scanNextToken_dispatchContent,hg,hf,alias_loop k v hk hv,hr,alias_scan k v hk hv,alias_close k v hk hv,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma q_common (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 Common (stop k v) (qp k v) '?' := by
 rcases ending_gets k v hk hv with ⟨h0,h1,h2,h3,h7,h8,h9,h10,h11⟩
 have hs := AnchoredAliasSource.source_size k v hk hv
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,suffix,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs h0 h1 h2 h3 h7 h8 h9 h10 h11
 simp [ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,hs,h0,h1,h2,h3,h7,h8,h9,h10,h11,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma copy_common (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 Common (qo k v) (kp k v) 'c' := by
 rcases ending_gets k v hk hv with ⟨h0,h1,h2,h3,h7,h8,h9,h10,h11⟩
 have hs := AnchoredAliasSource.source_size k v hk hv
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,suffix,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs h0 h1 h2 h3 h7 h8 h9 h10 h11
 simp [ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,hs,h0,h1,h2,h3,h7,h8,h9,h10,h11,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma c_common (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 Common (ko k v) (cp k v) ':' := by
 rcases ending_gets k v hk hv with ⟨h0,h1,h2,h3,h7,h8,h9,h10,h11⟩
 have hs := AnchoredAliasSource.source_size k v hk hv
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,suffix,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs h0 h1 h2 h3 h7 h8 h9 h10 h11
 simp [ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,hs,h0,h1,h2,h3,h7,h8,h9,h10,h11,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma alias_common (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 Common (co k v) (ap k v) '*' := by
 rcases ending_gets k v hk hv with ⟨h0,h1,h2,h3,h7,h8,h9,h10,h11⟩
 have hs := AnchoredAliasSource.source_size k v hk hv
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,suffix,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs h0 h1 h2 h3 h7 h8 h9 h10 h11
 simp [ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,hs,h0,h1,h2,h3,h7,h8,h9,h10,h11,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma q_flag (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (isKeyCandidate (qp k v) && flowKeyPredecessorOk (qp k v) && flowKeyFollowerOk (qp k v))=true := by
 rcases ending_gets k v hk hv with ⟨h0,h1,h2,h3,h7,h8,h9,h10,h11⟩
 have hs := AnchoredAliasSource.source_size k v hk hv
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs h0 h1 h2 h3 h7 h8 h9 h10 h11
 simp [isKeyCandidate,flowKeyPredecessorOk,flowKeyFollowerOk,ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,
  scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.inFlow,ScannerState.peekAt?,ScannerState.peekAt?Loop,
  String.Pos.Raw.next,String.Pos.Raw.add_char_eq,hs,h1,h2,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,
  Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma c_flag (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 isValueCandidate (cp k v)=true := by
 rcases ending_gets k v hk hv with ⟨h0,h1,h2,h3,h7,h8,h9,h10,h11⟩
 have hs := AnchoredAliasSource.source_size k v hk hv
 simp only [AnchoredAliasSource.source,AnchoredWordSource.source,tailOffset,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hs h0 h1 h2 h3 h7 h8 h9 h10 h11
 simp [isValueCandidate,ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,
  scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.inFlow,ScannerState.peekAt?,ScannerState.peekAt?Loop,
  String.Pos.Raw.next,String.Pos.Raw.add_char_eq,hs,h8,h9,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,
  Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma q_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken (stop k v)=.ok (some (qo k v)) := by
 have hu : upd (qp k v)=qp k v := rfl
 apply stepBlock (q_preprocess k v hk hv) (q_common k v hk hv)
 rw [hu]
 simp [scanNextToken_dispatchBlockIndicators,q_flag k v hk hv,q_scan k v hk hv,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma copy_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken (qo k v)=.ok (some (ko k v)) := by
 have hb := letter_block (kp k v) 'c' (by simp [Letter])
 have hu : upd (kp k v)=kp k v := rfl
 apply stepContent (copy_preprocess k v hk hv) (copy_common k v hk hv)
 · rw [hu,hb.1]; rfl
 · rw [hu,hb.2.1]; rfl
 · rw [hu,letter_dispatch _ _ (by simp [Letter])]; exact copy_scan k v hk hv

lemma c_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken (ko k v)=.ok (some (co k v)) := by
 have hu : upd (cp k v)=cp k v := rfl
 apply stepBlock (c_preprocess k v hk hv) (c_common k v hk hv)
 rw [hu]
 simp [scanNextToken_dispatchBlockIndicators,c_flag k v hk hv,c_scan k v hk hv,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma alias_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken (co k v)=.ok (some (ao k v)) := by
 have hu : upd (ap k v)=ap k v := rfl
 apply stepContent (alias_preprocess k v hk hv) (alias_common k v hk hv)
 · rw [hu]; simp [scanNextToken_dispatchBlockIndicators,noneGood,pure,Except.pure]
 · rw [hu]; simp [scanNextToken_checkAdjacentValue,Except.isOk,Except.toBool]
 · rw [hu]; exact alias_dispatch k v hk hv

lemma next_eof (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken (ao k v)=.ok none := by
 have he : (ao k v).inputEnd≤(ao k v).offset := by
  rw [(ao_eof k v hk hv).1]; exact Nat.le_refl _
 have hp := preprocess_eof (ao k v) he (by rfl)
 simp [scanNextToken,hp,bind,Except.bind,pure,Pure.pure,Except.pure]

def finalTokens (k v : List Char) : Array (Positioned YamlToken) :=
 ((unwindIndents (ao k v) (-1)).emit .streamEnd).tokens
def filteredTokens (k v : List Char) : Array (Positioned YamlToken) :=
 (finalTokens k v).filter (fun t => t.val != .placeholder)

lemma final_checks (k v : List Char) :
 scanLoop_checkDanglingNode (ao k v)=.ok () ∧ scanLoop_checkFlowValueIndent (ao k v)=.ok () := by
 simp [ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,anchorPre,anchorOut,anchorScanOut,scalarPre,scalarOut,suffix,scanLoop_checkDanglingNode,scanLoop_checkFlowValueIndent,danglingNodePos?,underIndentedFlowValuePos?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,ScannerState.inFlow,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma final_loop (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) (n : Nat) :
 scanLoop (ao k v) (n+1)=.ok (finalTokens k v) := by
 rw [scanLoop,next_eof k v hk hv]
 have hc := final_checks k v
 simp only [show (ao k v).flowLevel=0 from rfl,show (ao k v).directivesPresent=false from rfl]
 simp [hc.1,hc.2,finalTokens]

def expectedTokens (k v : List Char) : Array (Positioned YamlToken) :=
 #[ExplicitWordExecution.tok (pos 0 0 0) .streamStart,ExplicitWordExecution.tok (pos 0 0 0) .blockMappingStart,
  ExplicitWordExecution.tok (pos 0 0 0) .key,ExplicitWordExecution.tok (pos 2 0 2) (.scalar (String.ofList k) .plain),
  ExplicitWordExecution.tok (pos (3+k.length) 1 0) .value,ExplicitWordExecution.tok (pos (5+k.length) 1 2) (.anchor "a"),
  ExplicitWordExecution.tok (pos (8+k.length) 1 5) (.scalar (String.ofList v) .plain),
  ExplicitWordExecution.tok (pos (tailOffset k v 1) 2 0) .key,
  ExplicitWordExecution.tok (pos (tailOffset k v 3) 2 2) (.scalar "copy" .plain),
  ExplicitWordExecution.tok (pos (tailOffset k v 8) 3 0) .value,
  ExplicitWordExecution.tok (pos (tailOffset k v 10) 3 2) (.alias "a"),
  ExplicitWordExecution.tok (pos (tailOffset k v 12) 3 4) .blockEnd,
  ExplicitWordExecution.tok (pos (tailOffset k v 12) 3 4) .streamEnd]

lemma filtered_shape (k v : List Char) : filteredTokens k v=expectedTokens k v := by
 simp [filteredTokens,finalTokens,expectedTokens,unwindIndents,unwindIndentsLoop,
  ScannerState.currentIndent,ao,ap,co,cp,cline,ko,kp,qo,qp,qline,stop,tailOffset,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,
  afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,ExplicitWordExecution.tok,
  Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma alias_word_fold (k v : List Char) (hk : Word k) (hv : Word v) (n : Nat) :
 scanLoop (initial k (suffix (body v))) (n+9)=scanLoop (ao k v) n := by
 cases k with
 | nil => exact False.elim (hk.1 rfl)
 | cons c ks =>
  cases v with
  | nil => exact False.elim (hv.1 rfl)
  | cons d vs =>
   calc
    _ = scanLoop (qout (c::ks) (suffix (body (d::vs)))) (n+8) := by rw [scanLoop,ExplicitWordPrefix.question_step _ _ hk.2]
    _ = scanLoop (kout (c::ks) (suffix (body (d::vs)))) (n+7) := by rw [scanLoop,ExplicitWordPrefix.key_step c ks _ hk.2]
    _ = scanLoop (cout (c::ks) (suffix (body (d::vs)))) (n+6) := by rw [scanLoop,ExplicitWordPrefix.colon_step _ _ hk.2]
    _ = scanLoop (anchorOut (c::ks) (body (d::vs))) (n+5) := by rw [scanLoop,anchor_step _ _ hk.2]
    _ = scanLoop (stop (c::ks) (d::vs)) (n+4) := by rw [scanLoop,first_value_step _ d vs hk.2 hv.2]
    _ = scanLoop (qo (c::ks) (d::vs)) (n+3) := by rw [scanLoop,q_step _ _ hk.2 hv.2]
    _ = scanLoop (ko (c::ks) (d::vs)) (n+2) := by rw [scanLoop,copy_step _ _ hk.2 hv.2]
    _ = scanLoop (co (c::ks) (d::vs)) (n+1) := by rw [scanLoop,c_step _ _ hk.2 hv.2]
    _ = scanLoop (ao (c::ks) (d::vs)) n := by rw [scanLoop,alias_step _ _ hk.2 hv.2]

lemma alias_word_filtered (k v : List Char) (hk : Word k) (hv : Word v) :
 scanFiltered (AnchoredAliasSource.source k v)=.ok (expectedTokens k v) := by
 have hs := AnchoredAliasSource.source_size k v hk.2 hv.2
 have hp := ExplicitWordPrefix.initial_peek k (suffix (body v)) hk.2
 have hbound : 10≤((AnchoredAliasSource.source k v).utf8ByteSize+1)*4 := by rw [hs]; omega
 obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hbound
 have hfuel : ((AnchoredAliasSource.source k v).utf8ByteSize+1)*4=(n+1)+9 := by omega
 have hscan : scan (AnchoredAliasSource.source k v)=.ok (finalTokens k v) := by
  unfold scan
  change scanLoop (match (initial k (suffix (body v))).peek? with
   | some '\uFEFF' => (initial k (suffix (body v))).consumeBOM | _ => initial k (suffix (body v))) _ = _
  rw [hp]
  change scanLoop (initial k (suffix (body v))) (((AnchoredAliasSource.source k v).utf8ByteSize+1)*4) = _
  rw [hfuel,alias_word_fold k v hk hv,final_loop k v hk.2 hv.2 n]
 simp only [scanFiltered,hscan]
 change (Except.ok (filteredTokens k v) : Except ScanError _)=.ok (expectedTokens k v)
 rw [filtered_shape]

#print axioms q_scan
#print axioms copy_scan
#print axioms alias_word_filtered
#print axioms alias_word_fold
end L4YAML.Tests.Guards.AnchoredAliasExecution
