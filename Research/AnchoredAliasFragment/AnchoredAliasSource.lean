module
public import Tests.Guards.Proofs.AnchoredWordExecution
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredAliasSource
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScalarProduction L4YAML.Proofs.Acceptance
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.ExplicitWordExecution
-- Blueprint 7.7: source-defined later alias → actual scan/fold and owner trace.
def ending : List Char := ['\n','?',' ','c','o','p','y','\n',':',' ','*','a']
def body (v : List Char) : List Char := v++ending
def source (k v : List Char) : String := AnchoredWordSource.source k (body v)

lemma ending_bytes : listByteSize ending=12 := by decide
lemma source_size (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 (source k v).utf8ByteSize=20+k.length+v.length := by
 rw [source,AnchoredWordSource.source,ExplicitWordPrefix.source_size k _ hk]
 simp only [AnchoredWordSource.suffix,listByteSize,body,listByteSize_append,word_bytes v hv,ending_bytes,
  show '&'.utf8Size=1 from by decide,show 'a'.utf8Size=1 from by decide,space_byte]
 omega

lemma word_before_question (cs v : List Char) (s : ScannerState)
 (hl : ∀ c ∈ cs, Letter c)
 (hc : ScannerSurfCorr s ⟨cs ++ '\n' :: '?' :: ' ' :: v,s.col⟩)
 (hpos : s.col ≠ 0) (hflow : s.inFlow = false) (hi : s.currentIndent = 0) :
 scanPlainScalar s = .ok (afterWord s cs) := by
 have hf := fuel_of_corr hc
 let fuel := (s.inputEnd-s.offset+1)*2
 have hbound : cs.length < fuel := by dsimp [fuel]; simp only [List.length_append, List.length_cons] at hf; omega
 obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le (show cs.length+1 ≤ fuel by omega)
 have heq : fuel = cs.length+(n+1) := by omega
 obtain ⟨hland,hloop⟩ := word_prefix cs ('\n' :: '?' :: ' ' :: v) s "" (n+1) 1 hl hc hpos
 have hstop : PlainBreakStopOk 1 1 ⟨'\n' :: '?' :: ' ' :: v,s.col+cs.length⟩ := by
  apply PlainBreakStopOk.underIndent _ ⟨'?' :: ' ' :: v,0⟩ ⟨'?' :: ' ' :: v,0⟩
   ⟨'?' :: ' ' :: v,0⟩ ⟨'?' :: ' ' :: v,0⟩ 0
  · exact .lf _ _
  · exact .nil _
  · exact .zero _
  · simp
  · exact .nil _
  · simp
  · simp
  · intro c h; simp at h; subst c; decide
  · decide
 have hend := collectPlainScalarLoop_breakStop (shift s cs.length) hland hstop
   (by simpa [shift, ScannerState.currentIndent, hi] using (show (1:Int)>s.currentIndent by omega)) (by decide) n (String.ofList cs) ""
 rw [ExplicitWordFragment.word_fold] at hloop
 simp only [String.empty_append] at hloop
 have he := hloop.trans (by simpa [shift] using hend)
 simp only [scanPlainScalar, hflow, Bool.false_eq_true, ite_false, hi]
 change (do
   let r ← collectPlainScalarLoop s "" "" fuel false 1 s.inputEnd
   pure { (r.state.emitAt s.currentPos (.scalar (trimTrailingWS r.content) .plain)) with
       simpleKeyAllowed := false, needIndentCheck := false }) = _
 rw [heq, he]
 simp [word_trim cs hl, afterWord, shift, bind, Except.bind, pure, Pure.pure, Except.pure]


#print axioms word_before_question
end L4YAML.Tests.Guards.AnchoredAliasSource

