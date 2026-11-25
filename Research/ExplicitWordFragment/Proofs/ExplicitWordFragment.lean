module
public import Tests.Guards.Proofs.OwnerExplicitKeyConsume
public import L4YAML.Proofs.Production.Acceptance.Plain
public import L4YAML.Parser.Composition
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.Acceptance
set_option maxHeartbeats 6000000

-- Blueprint 7.7: source-defined words → actual initialized scan → owner trace.
-- Alphabet membership is independent of scanner success and grammar derivability.
def Letter (c : Char) : Prop := c ∈ ['a','b','c','d','e','f','g','h','i','j','k','l','m',
 'n','o','p','q','r','s','t','u','v','w','x','y','z']
def Word (cs : List Char) : Prop := cs ≠ [] ∧ ∀ c ∈ cs, Letter c

def source (k v : List Char) : String := String.ofList ('?' :: ' ' :: (k ++ '\n' :: ':' :: ' ' :: v))

def shift (s : ScannerState) (n : Nat) : ScannerState :=
 { s with offset := s.offset+n, col := s.col+n }

lemma letter_facts {c : Char} (hc : Letter c) :
 c ≠ '#' ∧ c ≠ ':' ∧ c ≠ '\n' ∧ c ≠ '\r' ∧ isLineBreakBool c = false ∧
 isWhiteSpaceBool c = false ∧ isPlainSafeBool c false = true ∧
 c.utf8Size = 1 ∧ isIndicatorBool c = false ∧ (c == ' ' || c == '\t') = false := by
 simp only [Letter, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
 rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma shift_add (s : ScannerState) (a b : Nat) : shift (shift s a) b = shift s (a+b) := by
 simp [shift, Nat.add_assoc]

lemma advance_letter {s : ScannerState} {c : Char} (hp : s.peek? = some c) (hc : Letter c) :
 s.advance = shift s 1 := by
 have hm := peek_some_has_more hp
 have hg : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
  simpa [ScannerState.peek?, hm] using hp
 rcases letter_facts hc with ⟨_,_,hn,hcr,_,_,_,hu,_⟩
 simp [ScannerState.advance, hm, hg, hn, hcr, next_byteIdx, hu, shift]

lemma word_prefix (letters tail : List Char) (s : ScannerState) (content : String)
 (fuel ci : Nat) (hl : ∀ c ∈ letters, Letter c)
 (hc : ScannerSurfCorr s ⟨letters ++ tail,s.col⟩) (hpos : s.col ≠ 0) :
 ScannerSurfCorr (shift s letters.length) ⟨tail,s.col+letters.length⟩ ∧
 collectPlainScalarLoop s content "" (letters.length+fuel) false ci s.inputEnd =
 collectPlainScalarLoop (shift s letters.length)
  (letters.foldl (fun acc c => acc ++ String.singleton c) content) "" fuel false ci s.inputEnd := by
 induction letters generalizing s content with
 | nil => simpa [shift] using And.intro hc (Eq.refl (collectPlainScalarLoop s content "" fuel false ci s.inputEnd))
 | cons c cs ih =>
  have hh := hl c (by simp)
  have ht : ∀ d ∈ cs, Letter d := fun d hd => hl d (by simp [hd])
  rcases letter_facts hh with ⟨hhash,hcolon,hn,hcr,hlb,hws,hsafe,_⟩
  have hc0 : ScannerSurfCorr s ⟨c :: (cs ++ tail),s.col⟩ := by simpa using hc
  have hp := corr_peek_head hc0
  have ha := advance_letter hp hh
  have hca : ScannerSurfCorr s.advance ⟨cs ++ tail,s.advance.col⟩ := by
   have h := advance_non_newline_corr s c (cs++tail) hc0 (peek_some_has_more hp) hn hcr
   simpa [ha,shift] using h
  have hnz : s.advance.col ≠ 0 := by simp [ha,shift]
  obtain ⟨hland,heq⟩ := ih s.advance (content ++ String.singleton c) ht hca hnz
  have hstate : shift s.advance cs.length = shift s (c::cs).length := by
   rw [ha,shift_add]; congr 1; simp; omega
  have hcol : s.advance.col + cs.length = s.col+(c::cs).length := by simp [ha,shift]; omega
  have hterm : collectPlainScalar_terminates? c s content "" false = none := by
   simp [collectPlainScalar_terminates?, beq_iff_eq,hhash,hcolon,hpos]
  refine ⟨by simpa [hstate,hcol] using hland, ?_⟩
  rw [show (c::cs).length+fuel = (cs.length+fuel)+1 by simp; omega]
  rw [collectPlainScalarLoop]
  simp only [hp,hterm,hlb,hws,hsafe,Bool.false_eq_true,ite_false,ite_true]
  simpa [hstate,ha,shift,List.foldl_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using heq

lemma word_fold (cs : List Char) (acc : String) :
 cs.foldl (fun a c => a ++ String.singleton c) acc = acc ++ String.ofList cs := by
 induction cs generalizing acc with
 | nil => simp
 | cons c cs ih =>
  rw [List.foldl_cons, ih]
  change (acc ++ String.singleton c) ++ String.ofList cs = acc ++ String.ofList (c :: cs)
  rw [String.append_assoc]
  exact congrArg (acc ++ ·) (String.ofList_append (l₁ := [c]) (l₂ := cs)).symm

lemma word_trim (cs : List Char) (hl : ∀ c ∈ cs, Letter c) :
 trimTrailingWS (String.ofList cs) = String.ofList cs := by
 have hd : cs.reverse.dropWhile (fun c => c == ' ' || c == '\t') = cs.reverse := by
  cases hr : cs.reverse with
  | nil => simp
  | cons c rest =>
   have hc : c ∈ cs := List.mem_reverse.mp (by rw [hr]; simp)
   have hh := (letter_facts (hl c hc)).2.2.2.2.2.2.2.2.2
   simp [hh]
 simp [trimTrailingWS, hd]

def afterWord (s : ScannerState) (cs : List Char) : ScannerState :=
 let t := (shift s cs.length).emitAt s.currentPos (.scalar (String.ofList cs) .plain)
 {t with simpleKeyAllowed := false, needIndentCheck := false}

lemma word_eof (cs : List Char) (s : ScannerState)
 (hl : ∀ c ∈ cs, Letter c) (hc : ScannerSurfCorr s ⟨cs,s.col⟩)
 (hpos : s.col ≠ 0) (hflow : s.inFlow = false) :
 scanPlainScalar s = .ok (afterWord s cs) := by
 have hf := fuel_of_corr hc
 let fuel := (s.inputEnd-s.offset+1)*2
 have hbound : cs.length < fuel := by dsimp [fuel]; simp only at hf; omega
 obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le (show cs.length+1 ≤ fuel by omega)
 have heq : fuel = cs.length+(n+1) := by omega
 obtain ⟨hland,hloop⟩ := word_prefix cs [] s "" (n+1)
   (max 0 (s.currentIndent+1)).toNat hl (by simpa using hc) hpos
 rw [word_fold] at hloop
 have hp := peek_none_of_corr hland
 rw [collectPlainScalarLoop] at hloop
 simp only [hp, String.empty_append] at hloop
 simp only [scanPlainScalar, hflow, Bool.false_eq_true, ite_false]
 change (do
   let r ← collectPlainScalarLoop s "" "" fuel false
      (max 0 (s.currentIndent+1)).toNat s.inputEnd
   pure { (r.state.emitAt s.currentPos (.scalar (trimTrailingWS r.content) .plain)) with
       simpleKeyAllowed := false, needIndentCheck := false }) = _
 rw [heq, hloop]
 simp [word_trim cs hl, afterWord, shift, bind, Except.bind, pure, Pure.pure, Except.pure]

lemma word_before_colon (cs v : List Char) (s : ScannerState)
 (hl : ∀ c ∈ cs, Letter c)
 (hc : ScannerSurfCorr s ⟨cs ++ '\n' :: ':' :: ' ' :: v,s.col⟩)
 (hpos : s.col ≠ 0) (hflow : s.inFlow = false) (hi : s.currentIndent = 0) :
 scanPlainScalar s = .ok (afterWord s cs) := by
 have hf := fuel_of_corr hc
 let fuel := (s.inputEnd-s.offset+1)*2
 have hbound : cs.length < fuel := by dsimp [fuel]; simp only [List.length_append, List.length_cons] at hf; omega
 obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le (show cs.length+1 ≤ fuel by omega)
 have heq : fuel = cs.length+(n+1) := by omega
 obtain ⟨hland,hloop⟩ := word_prefix cs ('\n' :: ':' :: ' ' :: v) s "" (n+1) 1 hl hc hpos
 have hstop : PlainBreakStopOk 1 1 ⟨'\n' :: ':' :: ' ' :: v,s.col+cs.length⟩ := by
  apply PlainBreakStopOk.underIndent _ ⟨':' :: ' ' :: v,0⟩ ⟨':' :: ' ' :: v,0⟩
   ⟨':' :: ' ' :: v,0⟩ ⟨':' :: ' ' :: v,0⟩ 0
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
 rw [word_fold] at hloop
 simp only [String.empty_append] at hloop
 have he := hloop.trans (by simpa [shift] using hend)
 simp only [scanPlainScalar, hflow, Bool.false_eq_true, ite_false, hi]
 change (do
   let r ← collectPlainScalarLoop s "" "" fuel false 1 s.inputEnd
   pure { (r.state.emitAt s.currentPos (.scalar (trimTrailingWS r.content) .plain)) with
       simpleKeyAllowed := false, needIndentCheck := false }) = _
 rw [heq, he]
 simp [word_trim cs hl, afterWord, shift, bind, Except.bind, pure, Pure.pure, Except.pure]

#print axioms word_eof
#print axioms word_before_colon
end L4YAML.Tests.Guards.ExplicitWordFragment
