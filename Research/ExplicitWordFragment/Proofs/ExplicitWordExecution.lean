module
public import Tests.Guards.Proofs.ExplicitWordFragment
public import Tests.Guards.Proofs.RootInhabited
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ExplicitWordExecution
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance L4YAML.Proofs.ScalarProduction
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.RootInhabited
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

@[simp] lemma question_byte : '?'.utf8Size = 1 := by decide
@[simp] lemma space_byte : ' '.utf8Size = 1 := by decide
@[simp] lemma lf_byte : '\n'.utf8Size = 1 := by decide
@[simp] lemma colon_byte : ':'.utf8Size = 1 := by decide
@[simp] lemma raw_zero : (⟨0⟩ : String.Pos.Raw) = 0 := rfl

lemma word_bytes (cs : List Char) (h : ∀ c ∈ cs, Letter c) : listByteSize cs = cs.length := by
 induction cs with
 | nil => rfl
 | cons c cs ih =>
  simp only [listByteSize,List.length_cons, (letter_facts (h c (by simp))).2.2.2.2.2.2.2.1]
  rw [ih (fun d hd => h d (by simp [hd]))]; omega

lemma get_boundary (input : String) (pre : List Char) (c : Char) (tail : List Char)
 (h : input.toList = pre ++ c :: tail) :
 String.Pos.Raw.get input ⟨listByteSize pre⟩ = c := by
 rw [get_eq_utf8GetAux,h]
 simpa using utf8GetAux_at_boundary pre c tail 0

lemma source_size (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (source k v).utf8ByteSize = 5+k.length+v.length := by
 simp only [utf8ByteSize_eq_listByteSize,source,String.toList_ofList,listByteSize,listByteSize_append,
  word_bytes k hk,word_bytes v hv,question_byte,space_byte,lf_byte,colon_byte]; omega

lemma source_zero (k v : List Char) : String.Pos.Raw.get (source k v) (0 : String.Pos.Raw) = '?' := by
 simpa [listByteSize,source] using get_boundary (source k v) [] '?' (' '::(k++'\n'::':'::' '::v)) (by simp [source])
lemma source_one (k v : List Char) : String.Pos.Raw.get (source k v) ⟨1⟩ = ' ' := by
 simpa [listByteSize,source] using get_boundary (source k v) ['?'] ' ' (k++'\n'::':'::' '::v) (by simp [source])
lemma source_key (c : Char) (ks v : List Char) : String.Pos.Raw.get (source (c::ks) v) ⟨2⟩ = c := by
 simpa [listByteSize,source] using get_boundary (source (c::ks) v) ['?',' '] c (ks++'\n'::':'::' '::v) (by simp [source])
lemma source_lf (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 String.Pos.Raw.get (source k v) ⟨2+k.length⟩ = '\n' := by
 simpa [listByteSize_append,listByteSize,word_bytes k hk,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
  get_boundary (source k v) (['?',' ']++k) '\n' (':'::' '::v) (by simp [source])
lemma source_colon (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 String.Pos.Raw.get (source k v) ⟨3+k.length⟩ = ':' := by
 simpa [listByteSize_append,listByteSize,word_bytes k hk,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
  get_boundary (source k v) (['?',' ']++k++['\n']) ':' (' '::v) (by simp [source])
lemma source_space (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 String.Pos.Raw.get (source k v) ⟨4+k.length⟩ = ' ' := by
 simpa [listByteSize_append,listByteSize,word_bytes k hk,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
  get_boundary (source k v) (['?',' ']++k++['\n',':']) ' ' v (by simp [source])
lemma source_value (k : List Char) (d : Char) (vs : List Char) (hk : ∀ c ∈ k, Letter c) :
 String.Pos.Raw.get (source k (d::vs)) ⟨5+k.length⟩ = d := by
 simpa [listByteSize_append,listByteSize,word_bytes k hk,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
  get_boundary (source k (d::vs)) (['?',' ']++k++['\n',':',' ']) d vs (by simp [source])

def pos (off line col : Nat) : YamlPos := ⟨off,line,col⟩
def tok (p : YamlPos) (t : YamlToken) : Positioned YamlToken := ⟨p,t,p⟩
def initial (k v : List Char) : ScannerState := (ScannerState.mk' (source k v)).emit .streamStart

def qpre (k v : List Char) : ScannerState :=
 {initial k v with
  needIndentCheck := false,
  tokens := #[(tok (pos 0 0 0) .streamStart),(tok (pos 0 0 0) .placeholder),(tok (pos 0 0 0) .placeholder)],
  simpleKey := {possible := true, tokenIndex := 1, pos := pos 0 0 0}}
def qstart (k v : List Char) : ScannerState := {qpre k v with allowDirectives:=false,documentEverStarted:=true}
def qout (k v : List Char) : ScannerState :=
 {qstart k v with
  offset:=1,col:=1,
  indents:=#[⟨-1,false⟩,⟨0,false⟩],pendingKeys:=#[none,some 0],
  tokens := (qstart k v).tokens.push (tok (pos 0 0 0) .blockMappingStart) |>.push (tok (pos 0 0 0) .key),
  simpleKey:={},explicitKeyLine:=some 0,explicitKeyCol:=0}
def kpre (k v : List Char) : ScannerState :=
 {qout k v with
  offset:=2,col:=2,
  tokens := (qout k v).tokens.push (tok (pos 2 0 2) .placeholder) |>.push (tok (pos 2 0 2) .placeholder),
  simpleKey:={possible:=true,tokenIndex:=5,pos:=pos 2 0 2}}
def kout (k v : List Char) : ScannerState := afterWord (kpre k v) k

def cpre (k v : List Char) : ScannerState :=
 {kout k v with
  offset:=3+k.length,line:=1,col:=0,simpleKeyAllowed:=true,
  tokens := (kout k v).tokens.push (tok (pos (3+k.length) 1 0) .placeholder) |>.push (tok (pos (3+k.length) 1 0) .placeholder),
  simpleKey:={possible:=true,tokenIndex:=8,pos:=pos (3+k.length) 1 0,endLine:=1}}
def cout (k v : List Char) : ScannerState :=
 {cpre k v with
  offset:=4+k.length,col:=1,pendingKeys:=#[none,none],simpleKey:={},explicitKeyLine:=none,explicitKeyCol:= -1,
  tokens := (cpre k v).tokens.push (tok (pos (3+k.length) 1 0) .value)}
def vpre (k v : List Char) : ScannerState :=
 {cout k v with
  offset:=5+k.length,col:=2,
  tokens := (cout k v).tokens.push (tok (pos (5+k.length) 1 2) .placeholder) |>.push (tok (pos (5+k.length) 1 2) .placeholder),
  simpleKey:={possible:=true,tokenIndex:=11,pos:=pos (5+k.length) 1 2,endLine:=1}}
def vout (k v : List Char) : ScannerState := afterWord (vpre k v) v

lemma skip_spaces_stop (s : ScannerState) (hp : s.peek? ≠ some ' ') : ∀ n, skipSpacesLoop s n = s := by
 intro n; cases n with
 | zero => simp [skipSpacesLoop]
 | succ n => cases h : s.peek? <;> simp_all [skipSpacesLoop]

lemma skip_whitespace_stop (s : ScannerState) {c : Char} (hp : s.peek? = some c)
 (hw : isWhiteSpaceBool c = false) : ∀ n, skipWhitespaceLoop s n = s := by
 intro n; cases n <;> simp [skipWhitespaceLoop,hp,hw]

lemma skip_content_loop_stop (s : ScannerState) {c : Char} (hp : s.peek? = some c)
 (hspace : c ≠ ' ') (htab : c ≠ '\t') (hhash : c ≠ '#')
 (hw : isWhiteSpaceBool c = false) (hb : isLineBreakBool c = false) :
 ∀ n, skipToContentLoop s n = .ok s := by
 have hsp : skipSpaces s = s := skip_spaces_stop s (by simpa [hp] using hspace) _
 have hws : skipWhitespace s = s := skip_whitespace_stop s hp hw _
 have hsw : skipToContentWs s = .ok s := by
  simp only [skipToContentWs,hsp,hws,hp]
  split
  · split <;> simp_all [bind,Except.bind]
  · rfl
 have hsc : skipToContentComment s = s := by simp [skipToContentComment,hp,hhash,beq_iff_eq]
 intro n; cases n with
 | zero => simp [skipToContentLoop]
 | succ n => simp [skipToContentLoop,hsw,hsc,hp,hb,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma skip_content_stop (s : ScannerState) {c : Char} (hp : s.peek? = some c)
 (hspace : c ≠ ' ') (htab : c ≠ '\t') (hhash : c ≠ '#')
 (hw : isWhiteSpaceBool c = false) (hb : isLineBreakBool c = false) :
 skipToContent s = .ok s := skip_content_loop_stop s hp hspace htab hhash hw hb _

lemma initial_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken_preprocess (initial k v) = .ok (some (qpre k v,'?')) := by
 have h0 := source_zero k v
 have hs := source_size k v hk hv
 have hm : 0 < 5+k.length+v.length := by omega
 have hp : (initial k v).peek? = some '?' := by
  simp [initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,hs,h0,hm]
 have hsk := skip_content_stop (initial k v) hp (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [scanNextToken_preprocess,hsk]
 simp [initial,qpre,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,
  ScannerState.currentPos,ScannerState.hasMore,ScannerState.peek?,hs,h0,hm,
  ScannerState.inFlow,ScannerState.currentIndent,
  unwindIndents,unwindIndentsLoop,saveSimpleKey,closeStaleExplicitKey,
  bind,Except.bind,pure,Pure.pure,Except.pure,pos,tok]

lemma question_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanKey (qstart k v) = .ok (qout k v) := by
 have h0 := source_zero k v
 have h1 := source_one k v
 have hs := source_size k v hk hv
 have hm0 : 0 < 5+k.length+v.length := by omega
 have hm1 : 1 < 5+k.length+v.length := by omega
 simp [scanKey,scanKeyValidate,qstart,qpre,qout,initial,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.inFlow,ScannerState.currentIndent,ScannerState.peek?,ScannerState.advance,
  ScannerState.hasTabInPrecedingWhitespace,ScannerState.hasTabInPrecedingWhitespaceLoop,
  ScannerState.markerOnLine,lastTokenIsNodePropertyOnLine,lastRealToken?,YamlToken.isNodeProperty,atSequenceIndent,
  pushMappingIndent,String.Pos.Raw.next,next_byteIdx,hs,h0,h1,hm0,hm1,
  bind,Except.bind,pure,Pure.pure,Except.pure,pos,tok]

lemma advance_unit {s : ScannerState} {c : Char} (hp : s.peek? = some c)
 (hn : c ≠ '\n') (hr : c ≠ '\r') (hu : c.utf8Size = 1) : s.advance = shift s 1 := by
 have hm := peek_some_has_more hp
 have hg : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by simpa [ScannerState.peek?,hm] using hp
 simp [ScannerState.advance,hm,hg,hn,hr,next_byteIdx,hu,shift]

lemma skip_one_space (s : ScannerState) {c : Char} (hp : s.peek? = some ' ')
 (ha : s.advance.peek? = some c) (hn : s.needIndentCheck = false)
 (hsp : c ≠ ' ') (htab : c ≠ '\t') (hhash : c ≠ '#')
 (hw : isWhiteSpaceBool c = false) (hb : isLineBreakBool c = false) :
 skipToContent s = .ok s.advance := by
 have hm := peek_some_has_more hp
 have hws : skipWhitespace s = s.advance := by
  have hle : 1 ≤ s.inputEnd-s.offset := by omega
  obtain ⟨n,he⟩ := Nat.exists_eq_add_of_le hle
  unfold skipWhitespace
  rw [show s.inputEnd-s.offset=n+1 by omega, skipWhitespaceLoop]
  simp only [hp,isWhiteSpaceBool,beq_self_eq_true,Bool.true_or,ite_true]
  exact skip_whitespace_stop s.advance ha hw n
 have hsw : skipToContentWs s = .ok s.advance := by simp [skipToContentWs,hn,hws]
 have hsc : skipToContentComment s.advance = s.advance := by simp [skipToContentComment,ha,hhash]
 unfold skipToContent
 rw [skipToContentLoop]
 simp [hsw,hsc,ha,hb,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma key_preprocess (c : Char) (ks v : List Char)
 (hk : ∀ d ∈ c::ks, Letter d) (hv : ∀ d ∈ v, Letter d) :
 scanNextToken_preprocess (qout (c::ks) v) = .ok (some (kpre (c::ks) v,c)) := by
 have h1 := source_one (c::ks) v
 have h2 := source_key c ks v
 have hs := source_size (c::ks) v hk hv
 have hm1 : 1 < 5+(c::ks).length+v.length := by omega
 have hm2 : 2 < 5+(c::ks).length+v.length := by omega
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

lemma chars_suffix (input : String) (pre suf : List Char) (hsplit : input.toList = pre ++ suf) :
 CharsFromOffset input (listByteSize pre) suf := by
 induction suf generalizing pre with
 | nil =>
  apply CharsFromOffset.at_end
  rw [utf8ByteSize_eq_listByteSize,hsplit,listByteSize_append]; simp [listByteSize]
 | cons c cs ih =>
  apply CharsFromOffset.cons
  · rw [utf8ByteSize_eq_listByteSize,hsplit,listByteSize_append]
    simp [listByteSize]; have := Char.utf8Size_pos c; omega
  · exact get_boundary input pre c cs hsplit
  · rw [next_byteIdx,get_boundary input pre c cs hsplit]
    rw [show listByteSize pre+c.utf8Size=listByteSize (pre++[c]) by simp [listByteSize_append,listByteSize]]
    exact ih (pre++[c]) (by rw [hsplit,List.append_assoc]; rfl)

lemma corr_at_prefix (s : ScannerState) (pre tail : List Char)
 (hi : s.input.toList = pre++tail) (he : s.inputEnd = s.input.utf8ByteSize)
 (ho : listByteSize pre = s.offset)
 (hind : ∀ i (h:i<s.indents.size), 0<i → s.indents[i].column≥0) :
 ScannerSurfCorr s ⟨tail,s.col⟩ :=
 ⟨by rw [←ho]; exact chars_suffix s.input pre tail hi,rfl,he,⟨pre,hi,ho⟩,hind⟩

lemma key_corr (k v : List Char) : ScannerSurfCorr (kpre k v) ⟨k++'\n'::':'::' '::v,2⟩ := by
 apply corr_at_prefix (kpre k v) ['?',' ']
 · simp [kpre,qout,qstart,qpre,initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,source]
 · rfl
 · simp [kpre,listByteSize]
 · intro i hi hp
   simp [kpre,qout] at hi ⊢
   have : i=1 := by omega
   subst i; simp

lemma key_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 scanPlainScalar (kpre k v) = .ok (kout k v) :=
 word_before_colon k v (kpre k v) hk (key_corr k v) (by simp [kpre]) (by rfl) (by rfl)

lemma value_corr (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 ScannerSurfCorr (vpre k v) ⟨v,2⟩ := by
 apply corr_at_prefix (vpre k v) (['?',' ']++k++['\n',':',' '])
 · simp [vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,ScannerState.mk',source,afterWord,shift,ScannerState.emit,ScannerState.emitAt]
 · rfl
 · simp [vpre,listByteSize_append,listByteSize,word_bytes k hk,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
 · intro i hi hp
   simp [vpre,cout,cpre,kout,kpre,qout,afterWord,shift,ScannerState.emitAt] at hi ⊢
   have : i=1 := by omega
   subst i; simp

lemma value_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanPlainScalar (vpre k v) = .ok (vout k v) :=
 word_eof v (vpre k v) hv (value_corr k v hk) (by simp [vpre]) (by rfl)

lemma letter_dispatch (s : ScannerState) (c : Char) (hc : Letter c) :
 scanNextToken_dispatchContent s c = scanPlainScalar s := by
 have hprint : isPrintableBool c = true := by
  simp only [Letter,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
 simp only [Letter,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hc
 rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 all_goals simp [scanNextToken_dispatchContent,canStartPlainScalarBool,isIndicatorBool,isPlainSafeBool,
    isWhiteSpaceBool,isSpaceBool,isTabBool,isLineBreakBool,isLineFeedBool,isCarriageReturnBool,hprint,
    bind,Except.bind,pure,Pure.pure,Except.pure]

lemma advance_lf {s : ScannerState} (hp : s.peek? = some '\n') :
 s.advance = {s with offset:=s.offset+1,line:=s.line+1,col:=0} := by
 have hm := peek_some_has_more hp
 have hg : String.Pos.Raw.get s.input ⟨s.offset⟩ = '\n' := by simpa [ScannerState.peek?,hm] using hp
 simp [ScannerState.advance,hm,hg,next_byteIdx]

def newlineState (k v : List Char) : ScannerState :=
 {kout k v with
  offset:=3+k.length,line:=1,col:=0,needIndentCheck:=true,simpleKeyAllowed:=true}

lemma colon_skip (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 skipToContent (kout k v) = .ok (newlineState k v) := by
 have h2 := source_lf k v hk
 have h3 := source_colon k v hk
 have hs := source_size k v hk hv
 have hm2 : 2+k.length < 5+k.length+v.length := by omega
 have hm3 : 3+k.length < 5+k.length+v.length := by omega
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

lemma colon_preprocess (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken_preprocess (kout k v) = .ok (some (cpre k v,':')) := by
 have hsk := colon_skip k v hk hv
 have h3 := source_colon k v hk
 have h4 := source_space k v hk
 have hs := source_size k v hk hv
 have hm3 : 3+k.length < 5+k.length+v.length := by omega
 have hm4 : 4+k.length < 5+k.length+v.length := by omega
 simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hm3 hm4 h3 h4
 rw [scanNextToken_preprocess,hsk]
 simp [newlineState,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.hasMore,ScannerState.peek?,ScannerState.peekAt?,ScannerState.peekAt?Loop,
  ScannerState.inFlow,ScannerState.currentIndent,unwindIndents,unwindIndentsLoop,
  saveSimpleKey,closeStaleExplicitKey,PendingKeys.staleGate,PendingKeys.indicatorAt,
  String.Pos.Raw.next,String.Pos.Raw.add_char_eq,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,isLineBreakBool,isLineFeedBool,isCarriageReturnBool,hs,h3,h4,hm3,hm4,pos,tok,
  bind,Except.bind,pure,Pure.pure,Except.pure,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma source_prev_colon (k v : List Char) (hk : ∀ c ∈ k, Letter c) :
 String.Pos.Raw.prev (source k v) ⟨3+k.length⟩ = ⟨2+k.length⟩ := by
 have h := prev_next_with_prefix (source k v) (['?',' ']++k) '\n' (':'::' '::v) (by simp [source])
 have hg := get_boundary (source k v) (['?',' ']++k) '\n' (':'::' '::v) (by simp [source])
 rw [String.Pos.Raw.next,hg,String.Pos.Raw.add_char_eq] at h
 simpa [listByteSize_append,listByteSize,word_bytes k hk,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

lemma colon_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanValue (cpre k v) = .ok (cout k v) := by
 have h2 := source_lf k v hk
 have h3 := source_colon k v hk
 have h4 := source_space k v hk
 have hprev := source_prev_colon k v hk
 have hs := source_size k v hk hv
 have hm3 : 3+k.length < 5+k.length+v.length := by omega
 have hm4 : 4+k.length < 5+k.length+v.length := by omega
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

lemma value_preprocess (k : List Char) (d : Char) (vs : List Char)
 (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ d::vs, Letter c) :
 scanNextToken_preprocess (cout k (d::vs)) = .ok (some (vpre k (d::vs),d)) := by
 have h4 := source_space k (d::vs) hk
 have h5 := source_value k d vs hk
 have hs := source_size k (d::vs) hk hv
 have hm4 : 4+k.length < 5+k.length+(d::vs).length := by omega
 have hm5 : 5+k.length < 5+k.length+(d::vs).length := by simp
 simp only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hm4 hm5 h4 h5 hs
 have hp : (cout k (d::vs)).peek? = some ' ' := by
  simp [cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,
   ScannerState.emitAt,ScannerState.peek?,hs,h4,hm4,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have had := advance_unit hp (by decide) (by decide) (by decide)
 have ha : (cout k (d::vs)).advance.peek? = some d := by
  rw [had]
  simp [cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,
   ScannerState.emitAt,ScannerState.peek?,hs,h5,hm5,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 have hf := letter_facts (hv d (by simp))
 have hwhite := hf.2.2.2.2.2.2.2.2.2
 simp only [Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hwhite
 have hsk := skip_one_space (cout k (d::vs)) hp ha (by rfl) hwhite.1 hwhite.2 hf.1 hf.2.2.2.2.2.1 hf.2.2.2.2.1
 rw [scanNextToken_preprocess,hsk,had]
 simp [vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.hasMore,ScannerState.peek?,ScannerState.inFlow,saveSimpleKey,closeStaleExplicitKey,
  hs,h5,hm5,pos,tok,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma preprocess_eof (s : ScannerState) (he : s.inputEnd ≤ s.offset) (hn : s.needIndentCheck=false) :
 scanNextToken_preprocess s = .ok none := by
 have hp : s.peek?=none := by simp [ScannerState.peek?,Nat.not_lt.mpr he]
 simp [scanNextToken_preprocess,skipToContent,skipToContentLoop,skipToContentWs,hn,
  skipWhitespace,skipWhitespaceLoop,Nat.sub_eq_zero_of_le he,skipToContentComment,hp,
  ScannerState.hasMore,Nat.not_lt.mpr he,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma value_eof (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (vout k v).offset=(source k v).utf8ByteSize ∧
 scanNextToken (vout k v) = .ok none := by
 have hs := source_size k v hk hv
 have hoff : (vout k v).offset=(source k v).utf8ByteSize := by
  simp [vout,vpre,afterWord,shift,ScannerState.emitAt,hs]
 refine ⟨hoff,?_⟩
 have he : (vout k v).inputEnd ≤ (vout k v).offset := by
  rw [hoff]; exact Nat.le_refl _
 have hp := preprocess_eof (vout k v) he (by rfl)
 simp [scanNextToken,hp,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma common_question (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 Common (initial k v) (qpre k v) '?' := by
 have h0 := source_zero k v
 have hs := source_size k v hk hv
 have hm : 0<5+k.length+v.length := by omega
 simp [Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,h0,hs,hm]

lemma common_key (k v : List Char) (c : Char) (hc : Letter c) :
 Common (qout k v) (kpre k v) c := by
 have hi := (letter_facts hc).2.2.2.2.2.2.2.2.1
 simp only [isIndicatorBool,decide_eq_false_iff_not,List.mem_cons,List.mem_singleton,not_or] at hi
 simp_all [Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma common_colon (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 Common (kout k v) (cpre k v) ':' := by
 have h3 := source_colon k v hk
 have hs := source_size k v hk hv
 have hm : 3+k.length<5+k.length+v.length := by omega
 simp [Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure,h3,hs,hm]

lemma common_value (k v : List Char) (c : Char) (hc : Letter c) :
 Common (cout k v) (vpre k v) c := by
 have hi := (letter_facts hc).2.2.2.2.2.2.2.2.1
 simp only [isIndicatorBool,decide_eq_false_iff_not,List.mem_cons,List.mem_singleton,not_or] at hi
 simp_all [Common,upd,noneGood,scanNextToken_checkDanglingNode,scanNextToken_checkFlowValueIndent,scanNextToken_dispatchStructural,scanNextToken_checkNoPendingDirectives,scanNextToken_checkBareDocument,scanNextToken_dispatchFlowIndicators,scanNextToken_checkFlowAdjacency,danglingNodePos?,underIndentedFlowValuePos?,ScannerState.inFlow,ScannerState.currentIndent,atDocumentStart,atDocumentEnd,ScannerState.peekAt?,ScannerState.peekAt?Loop,ScannerState.hasMore,ScannerState.peek?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma letter_block (s : ScannerState) (c : Char) (hc : Letter c) :
 scanNextToken_dispatchBlockIndicators s c = .ok none ∧
 scanNextToken_checkAdjacentValue s c = .ok () ∧ ScalarGuard c := by
 have hi := (letter_facts hc).2.2.2.2.2.2.2.2.1
 simp only [isIndicatorBool,decide_eq_false_iff_not,List.mem_cons,List.mem_singleton,not_or] at hi
 simp_all [scanNextToken_dispatchBlockIndicators,scanNextToken_checkAdjacentValue,ScalarGuard,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma question_flag (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (isKeyCandidate (qstart k v) && flowKeyPredecessorOk (qstart k v) && flowKeyFollowerOk (qstart k v)) = true := by
 have h0 := source_zero k v
 have h1 := source_one k v
 have hs := source_size k v hk hv
 have hm0 : 0<5+k.length+v.length := by omega
 have hm1 : 1<5+k.length+v.length := by omega
 simp [isKeyCandidate,flowKeyPredecessorOk,flowKeyFollowerOk,qstart,qpre,initial,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.inFlow,
  ScannerState.peekAt?,ScannerState.peekAt?Loop,String.Pos.Raw.next,String.Pos.Raw.add_char_eq,
  hs,h0,h1,hm0,hm1,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool]

lemma colon_flag (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 isValueCandidate (cpre k v) = true := by
 have h3 := source_colon k v hk
 have h4 := source_space k v hk
 have hs := source_size k v hk hv
 have hm3 : 3+k.length<5+k.length+v.length := by omega
 have hm4 : 4+k.length<5+k.length+v.length := by omega
 simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hm3 hm4 h3 h4
 simp [isValueCandidate,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.inFlow,
  ScannerState.peekAt?,ScannerState.peekAt?Loop,String.Pos.Raw.next,String.Pos.Raw.add_char_eq,
  hs,h3,h4,hm3,hm4,isBlankBool,isWhiteSpaceBool,isSpaceBool,isTabBool,
  Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

lemma upd_q (k v : List Char) : upd (qpre k v) = qstart k v := by
 simp [upd,qstart,qpre,initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt]
lemma upd_k (k v : List Char) : upd (kpre k v) = kpre k v := by
 simp [upd,kpre,qout,qstart]
lemma upd_c (k v : List Char) : upd (cpre k v) = cpre k v := by
 simp [upd,cpre,kout,afterWord,shift,ScannerState.emitAt,kpre,qout,qstart]
lemma upd_v (k v : List Char) : upd (vpre k v) = vpre k v := by
 simp [upd,vpre,cout,cpre,kout,afterWord,shift,ScannerState.emitAt,kpre,qout,qstart]

lemma question_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken (initial k v) = .ok (some (qout k v)) := by
 apply stepBlock (initial_preprocess k v hk hv) (common_question k v hk hv)
 rw [upd_q]
 simp [scanNextToken_dispatchBlockIndicators,question_flag k v hk hv,question_scan k v hk hv,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma key_step (c : Char) (ks v : List Char)
 (hk : ∀ d ∈ c::ks, Letter d) (hv : ∀ d ∈ v, Letter d) :
 scanNextToken (qout (c::ks) v) = .ok (some (kout (c::ks) v)) := by
 have hc := hk c (by simp)
 have hb := letter_block (kpre (c::ks) v) c hc
 apply stepContent (key_preprocess c ks v hk hv) (common_key (c::ks) v c hc)
 · rw [upd_k,hb.1]; rfl
 · rw [upd_k,hb.2.1]; rfl
 · rw [upd_k,letter_dispatch _ _ hc]; exact key_scan _ _ hk

lemma colon_step (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanNextToken (kout k v) = .ok (some (cout k v)) := by
 apply stepBlock (colon_preprocess k v hk hv) (common_colon k v hk hv)
 rw [upd_c]
 simp [scanNextToken_dispatchBlockIndicators,colon_flag k v hk hv,colon_scan k v hk hv,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma value_step (k : List Char) (d : Char) (vs : List Char)
 (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ d::vs, Letter c) :
 scanNextToken (cout k (d::vs)) = .ok (some (vout k (d::vs))) := by
 have hc := hv d (by simp)
 have hb := letter_block (vpre k (d::vs)) d hc
 apply stepContent (value_preprocess k d vs hk hv) (common_value k (d::vs) d hc)
 · rw [upd_v,hb.1]; rfl
 · rw [upd_v,hb.2.1]; rfl
 · rw [upd_v,letter_dispatch _ _ hc]; exact value_scan _ _ hk hv

def finalTokens (k v : List Char) : Array (Positioned YamlToken) :=
 ((unwindIndents (vout k v) (-1)).emit .streamEnd).tokens
def filteredTokens (k v : List Char) : Array (Positioned YamlToken) :=
 (finalTokens k v).filter (fun t => t.val != .placeholder)

lemma final_checks (k v : List Char) :
 scanLoop_checkDanglingNode (vout k v) = .ok () ∧
 scanLoop_checkFlowValueIndent (vout k v) = .ok () := by
 simp [scanLoop_checkDanglingNode,scanLoop_checkFlowValueIndent,danglingNodePos?,underIndentedFlowValuePos?,qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok,lastRealTokenVal?,lastRealTokenIdx?,penultRealTokenVal?,lastRealToken?,penultRealToken?,trailingPropertyRun,prevRealIdx?,flowOpenIdxLoop,flowOpenIdx?,propsRunStart,trailingNodeRun?,propsBlockScanLoop,crossedPropsExcessIdx?,crossedPropsExcessPos?,propsBlockLineCrossLoop,runLineCrossPos?,runLineCrossDanglingPos?,slotHolderIdx?,nodeSlotAwaited,sameIndentSequenceOpenLoop,sameIndentSequenceOpen,trailingPropertyRunOnLine,lastTokenIsNodePropertyOnLine,YamlToken.isNodeProperty,YamlToken.isNodeBody,YamlToken.offersNodeSlot,YamlToken.completesFlowValue,YamlToken.isFlowOpen,YamlToken.isFlowClose,ScannerState.inFlow,Except.isOk,Except.toBool,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma final_loop (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) (n : Nat) :
 scanLoop (vout k v) (n+1) = .ok (finalTokens k v) := by
 rw [scanLoop,(value_eof k v hk hv).2]
 have hc := final_checks k v
 simp only [show (vout k v).flowLevel=0 from rfl,show (vout k v).directivesPresent=false from rfl]
 simp [hc.1,hc.2,finalTokens]

lemma initial_peek (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (initial k v).peek? = some '?' := by
 have hs := source_size k v hk hv
 have hm : 0<5+k.length+v.length := by omega
 simp [initial,ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.peek?,hs,source_zero k v,hm]

lemma scan_filtered (c d : Char) (ks vs : List Char)
 (hk : ∀ x ∈ c::ks, Letter x) (hv : ∀ x ∈ d::vs, Letter x) :
 scanFiltered (source (c::ks) (d::vs)) = .ok (filteredTokens (c::ks) (d::vs)) := by
 let k := c::ks
 let v := d::vs
 have h1 := question_step k v hk hv
 have h2 := key_step c ks v hk hv
 have h3 := colon_step k v hk hv
 have h4 := value_step k d vs hk hv
 have hp := initial_peek k v hk hv
 have hprefix (n : Nat) : scanLoop (initial k v) (n+4) = scanLoop (vout k v) n := by
  calc
   _ = scanLoop (qout k v) (n+3) := by rw [scanLoop,h1]
   _ = scanLoop (kout k v) (n+2) := by rw [scanLoop,h2]
   _ = scanLoop (cout k v) (n+1) := by rw [scanLoop,h3]
   _ = scanLoop (vout k v) n := by rw [scanLoop,h4]
 have hs := source_size k v hk hv
 have hbound : 5≤((source k v).utf8ByteSize+1)*4 := by rw [hs]; omega
 obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hbound
 have hfuel : ((source k v).utf8ByteSize+1)*4=(n+1)+4 := by omega
 have hscan : scan (source k v) = .ok (finalTokens k v) := by
  unfold scan
  change scanLoop (match (initial k v).peek? with
   | some '\uFEFF' => (initial k v).consumeBOM | _ => initial k v) _ = _
  rw [hp]
  change scanLoop (initial k v) (((source k v).utf8ByteSize+1)*4) = _
  rw [hfuel,hprefix,final_loop k v hk hv n]
 change scanFiltered (source k v) = .ok (filteredTokens k v)
 simp only [scanFiltered,hscan]
 rfl

def expectedTokens (k v : List Char) : Array (Positioned YamlToken) :=
 #[tok (pos 0 0 0) .streamStart,tok (pos 0 0 0) .blockMappingStart,tok (pos 0 0 0) .key,
  tok (pos 2 0 2) (.scalar (String.ofList k) .plain),tok (pos (3+k.length) 1 0) .value,
  tok (pos (5+k.length) 1 2) (.scalar (String.ofList v) .plain),
  tok (pos (5+k.length+v.length) 1 (2+v.length)) .blockEnd,
  tok (pos (5+k.length+v.length) 1 (2+v.length)) .streamEnd]

lemma filtered_shape (k v : List Char) : filteredTokens k v = expectedTokens k v := by
 simp [filteredTokens,finalTokens,expectedTokens,unwindIndents,unwindIndentsLoop,
  ScannerState.currentIndent,vout,vpre,cout,cpre,kout,kpre,qout,qstart,qpre,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,pos,tok]


lemma word_filtered (k v : List Char) (hk : Word k) (hv : Word v) :
 scanFiltered (source k v) = .ok (expectedTokens k v) := by
 cases k with
 | nil => exact False.elim (hk.1 rfl)
 | cons c ks =>
  cases v with
  | nil => exact False.elim (hv.1 rfl)
  | cons d vs => rw [scan_filtered c d ks vs hk.2 hv.2,filtered_shape]

lemma word_fold (k v : List Char) (hk : Word k) (hv : Word v) (n : Nat) :
 scanLoop (initial k v) (n+4) = scanLoop (vout k v) n := by
 cases k with
 | nil => exact False.elim (hk.1 rfl)
 | cons c ks =>
  cases v with
  | nil => exact False.elim (hv.1 rfl)
  | cons d vs =>
   calc
    _ = scanLoop (qout (c::ks) (d::vs)) (n+3) := by rw [scanLoop,question_step _ _ hk.2 hv.2]
    _ = scanLoop (kout (c::ks) (d::vs)) (n+2) := by rw [scanLoop,key_step c ks _ hk.2 hv.2]
    _ = scanLoop (cout (c::ks) (d::vs)) (n+1) := by rw [scanLoop,colon_step _ _ hk.2 hv.2]
    _ = scanLoop (vout (c::ks) (d::vs)) n := by rw [scanLoop,value_step _ d vs hk.2 hv.2]

#print axioms scan_filtered
#print axioms filtered_shape
end L4YAML.Tests.Guards.ExplicitWordExecution
