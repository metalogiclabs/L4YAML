module
public import Tests.Guards.Proofs.AnchoredAliasSource
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredAliasStates
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance L4YAML.Proofs.ScalarProduction
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.ExplicitWordExecution
open L4YAML.Tests.Guards.AnchoredWordSource (suffix)
open L4YAML.Tests.Guards.AnchoredWordExecution
open L4YAML.Tests.Guards.AnchoredAliasSource
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

-- Blueprint 7.7: every state is a concrete record over the actual source.
def tailOffset (k v : List Char) (n : Nat) : Nat := 8+k.length+v.length+n
def stop (k v : List Char) : ScannerState := afterWord (scalarPre k (body v)) v
def qline (k v : List Char) : ScannerState :=
 {stop k v with
  offset:=tailOffset k v 1,line:=2,col:=0,needIndentCheck:=true,simpleKeyAllowed:=true}
def qp (k v : List Char) : ScannerState :=
 {qline k v with
  needIndentCheck:=false,
  tokens:=(qline k v).tokens.push (tok (pos (tailOffset k v 1) 2 0) .placeholder) |>.push (tok (pos (tailOffset k v 1) 2 0) .placeholder),
  simpleKey:={possible:=true,tokenIndex:=15,pos:=pos (tailOffset k v 1) 2 0,endLine:=2}}
def qo (k v : List Char) : ScannerState :=
 {qp k v with
  offset:=tailOffset k v 2,col:=1,pendingKeys:=#[none,some 2],simpleKey:={},
  explicitKeyLine:=some 2,explicitKeyCol:=0,tokens:=(qp k v).tokens.push (tok (pos (tailOffset k v 1) 2 0) .key)}
def kp (k v : List Char) : ScannerState :=
 {qo k v with
  offset:=tailOffset k v 3,col:=2,
  tokens:=(qo k v).tokens.push (tok (pos (tailOffset k v 3) 2 2) .placeholder) |>.push (tok (pos (tailOffset k v 3) 2 2) .placeholder),
  simpleKey:={possible:=true,tokenIndex:=18,pos:=pos (tailOffset k v 3) 2 2,endLine:=2}}
def ko (k v : List Char) : ScannerState := afterWord (kp k v) ['c','o','p','y']
def cline (k v : List Char) : ScannerState :=
 {ko k v with
  offset:=tailOffset k v 8,line:=3,col:=0,needIndentCheck:=true,simpleKeyAllowed:=true}
def cp (k v : List Char) : ScannerState :=
 {cline k v with
  needIndentCheck:=false,
  tokens:=(cline k v).tokens.push (tok (pos (tailOffset k v 8) 3 0) .placeholder) |>.push (tok (pos (tailOffset k v 8) 3 0) .placeholder),
  simpleKey:={possible:=true,tokenIndex:=21,pos:=pos (tailOffset k v 8) 3 0,endLine:=3}}
def co (k v : List Char) : ScannerState :=
 {cp k v with
  offset:=tailOffset k v 9,col:=1,pendingKeys:=#[none,none],simpleKey:={},
  explicitKeyLine:=none,explicitKeyCol:= -1,tokens:=(cp k v).tokens.push (tok (pos (tailOffset k v 8) 3 0) .value)}
def ap (k v : List Char) : ScannerState :=
 {co k v with
  offset:=tailOffset k v 10,col:=2,
  tokens:=(co k v).tokens.push (tok (pos (tailOffset k v 10) 3 2) .placeholder) |>.push (tok (pos (tailOffset k v 10) 3 2) .placeholder),
  simpleKey:={possible:=true,tokenIndex:=24,pos:=pos (tailOffset k v 10) 3 2,endLine:=3}}
def ao (k v : List Char) : ScannerState :=
 {(shift (ap k v) 2).emitAt (ap k v).currentPos (.alias "a") with simpleKeyAllowed:=false}

def baseChars (k v : List Char) : List Char := ['?',' ']++k++['\n',':',' ','&','a',' ']++v
lemma source_chars (k v : List Char) : (AnchoredAliasSource.source k v).toList=baseChars k v++ending := by
 simp [AnchoredAliasSource.source,AnchoredWordSource.source,ExplicitWordFragment.source,
  suffix,body,baseChars,List.append_assoc]

lemma base_bytes (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 listByteSize (baseChars k v)=8+k.length+v.length := by
 simp [baseChars,listByteSize_append,listByteSize,word_bytes k hk,word_bytes v hv,
  show '&'.utf8Size=1 from by decide,show 'a'.utf8Size=1 from by decide]; omega

lemma get_ending (k v pre : List Char) (c : Char) (tail : List Char)
 (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) (h : ending=pre++c::tail) :
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v (listByteSize pre)⟩=c := by
 have hg := get_boundary (AnchoredAliasSource.source k v) (baseChars k v++pre) c tail
  (by rw [source_chars,h,List.append_assoc])
 simpa [tailOffset,listByteSize_append,base_bytes k v hk hv] using hg

lemma prev_ending (k v pre : List Char) (c : Char) (tail : List Char)
 (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) (hs : ending=pre++c::tail) :
 String.Pos.Raw.prev (AnchoredAliasSource.source k v) ⟨tailOffset k v (listByteSize pre+c.utf8Size)⟩=
 ⟨tailOffset k v (listByteSize pre)⟩ := by
 have split : (AnchoredAliasSource.source k v).toList=(baseChars k v++pre)++c::tail := by
  rw [source_chars,hs,List.append_assoc]
 have h := prev_next_with_prefix (AnchoredAliasSource.source k v) (baseChars k v++pre) c tail split
 have hg := get_boundary (AnchoredAliasSource.source k v) (baseChars k v++pre) c tail split
 rw [String.Pos.Raw.next,hg,String.Pos.Raw.add_char_eq] at h
 simpa [tailOffset,listByteSize_append,base_bytes k v hk hv,Nat.add_assoc] using h

lemma prev_question (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 String.Pos.Raw.prev (AnchoredAliasSource.source k v) ⟨tailOffset k v 1⟩=⟨tailOffset k v 0⟩ := by
 simpa only [show listByteSize []=0 from rfl,lf_byte,Nat.zero_add] using
  prev_ending k v [] '\n' _ hk hv rfl

lemma prev_colon (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 String.Pos.Raw.prev (AnchoredAliasSource.source k v) ⟨tailOffset k v 8⟩=⟨tailOffset k v 7⟩ := by
 simpa only [show listByteSize ['\n','?',' ','c','o','p','y']=7 from by decide,lf_byte] using
  prev_ending k v ['\n','?',' ','c','o','p','y'] '\n' _ hk hv rfl

lemma ending_gets (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 0⟩='\n' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 1⟩='?' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 2⟩=' ' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 3⟩='c' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 7⟩='\n' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 8⟩=':' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 9⟩=' ' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 10⟩='*' ∧
 String.Pos.Raw.get (AnchoredAliasSource.source k v) ⟨tailOffset k v 11⟩='a' := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · exact get_ending k v [] '\n' _ hk hv rfl
 · simpa only [show listByteSize ['\n']=1 from by decide] using get_ending k v ['\n'] '?' _ hk hv rfl
 · simpa only [show listByteSize ['\n','?']=2 from by decide] using get_ending k v ['\n','?'] ' ' _ hk hv rfl
 · simpa only [show listByteSize ['\n','?',' ']=3 from by decide] using get_ending k v ['\n','?',' '] 'c' _ hk hv rfl
 · simpa only [show listByteSize ['\n','?',' ','c','o','p','y']=7 from by decide] using
    get_ending k v ['\n','?',' ','c','o','p','y'] '\n' _ hk hv rfl
 · simpa only [show listByteSize ['\n','?',' ','c','o','p','y','\n']=8 from by decide] using
    get_ending k v ['\n','?',' ','c','o','p','y','\n'] ':' _ hk hv rfl
 · simpa only [show listByteSize ['\n','?',' ','c','o','p','y','\n',':']=9 from by decide] using
    get_ending k v ['\n','?',' ','c','o','p','y','\n',':'] ' ' _ hk hv rfl
 · simpa only [show listByteSize ['\n','?',' ','c','o','p','y','\n',':',' ']=10 from by decide] using
    get_ending k v ['\n','?',' ','c','o','p','y','\n',':',' '] '*' _ hk hv rfl
 · simpa only [show listByteSize ['\n','?',' ','c','o','p','y','\n',':',' ','*']=11 from by decide] using
    get_ending k v ['\n','?',' ','c','o','p','y','\n',':',' ','*'] 'a' _ hk hv rfl

lemma stop_corr (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 ScannerSurfCorr (stop k v) ⟨ending,5+v.length⟩ := by
 apply corr_at_prefix (stop k v) (baseChars k v)
 · exact source_chars k v
 · rfl
 · simp [base_bytes k v hk hv,stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,afterWord,shift,ScannerState.emitAt,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
 · intro i hi hp
   simp [stop,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,afterWord,shift,ScannerState.emitAt] at hi ⊢
   have : i=1 := by omega
   subst i; simp

lemma first_value_scan (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 scanPlainScalar (scalarPre k (body v))=.ok (stop k v) := by
 apply word_before_question v ['c','o','p','y','\n',':',' ','*','a'] (scalarPre k (body v)) hv
 · have hc : ScannerSurfCorr (scalarPre k (body v)) ⟨body v,(scalarPre k (body v)).col⟩ := by
    rw [show (scalarPre k (body v)).col=5 from rfl]
    exact scalar_corr k (body v) hk
   simpa only [body,ending] using hc
 · simp [scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,shift,ScannerState.emitAt]
 · rfl
 · rfl

lemma first_value_step (k : List Char) (d : Char) (vs : List Char)
 (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ d::vs, Letter c) :
 scanNextToken (anchorOut k (body (d::vs)))=.ok (some (stop k (d::vs))) := by
 have hd := hv d (by simp)
 have hb := letter_block (scalarPre k (body (d::vs))) d hd
 have hu : L4YAML.Tests.Guards.RootInhabited.upd (scalarPre k (body (d::vs)))=scalarPre k (body (d::vs)) := by
  simp [L4YAML.Tests.Guards.RootInhabited.upd,scalarPre,anchorOut,anchorScanOut,anchorPre,vpre,cout,cpre,kout,kpre,qout,qstart,afterWord,shift,ScannerState.emitAt]
 have hp : scanNextToken_preprocess (anchorOut k (body (d::vs)))=.ok (some (scalarPre k (body (d::vs)),d)) := by
  simpa only [body,List.cons_append] using scalar_preprocess k d (vs++ending) hk hd
 apply L4YAML.Tests.Guards.RootInhabited.stepContent hp (common_scalar k (body (d::vs)) d hd)
 · rw [hu,hb.1]; rfl
 · rw [hu,hb.2.1]; rfl
 · rw [hu,letter_dispatch _ _ hd]; exact first_value_scan _ _ hk hv

#print axioms first_value_step
end L4YAML.Tests.Guards.AnchoredAliasStates
