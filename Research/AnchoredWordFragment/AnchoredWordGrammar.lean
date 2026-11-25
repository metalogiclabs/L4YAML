module
public import Tests.Guards.Proofs.AnchoredWordSource
public import L4YAML.Proofs.Serialization.TraceOf.Document
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredWordGrammar
open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.AnchoredWordSource
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

-- Construct the grammar reading independently of scanner acceptance and
-- without invoking the inherited native-evaluation assertions on its fold path.
lemma letter_grammar {c : Char} (hc : Letter c) :
 isNsPlainSafe .flowOut c ∧ ¬isIndicatorProp c := by
 simp only [Letter,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hc
 rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [isNsPlainSafe,isNsChar,isIndicatorProp,isLineBreakProp,isLineFeedProp,
   isCarriageReturnProp,isWhiteSpaceProp,isSpaceProp,isTabProp,isPrintableProp] <;> decide

lemma word_tail (cs tail : List Char) (col : Nat) (hc : ∀ c ∈ cs, Letter c) :
 GStar (SNbNsPlainInLineEntry .flowOut) ⟨cs++tail,col⟩ ⟨tail,col+cs.length⟩ := by
 induction cs generalizing col with
 | nil => simpa using GStar.nil (P:=SNbNsPlainInLineEntry .flowOut) ⟨tail,col⟩
 | cons c cs ih =>
  have hl := hc c (by simp)
  have ht := ih (col+1) (fun d hd => hc d (by simp [hd]))
  have hstep : SNbNsPlainInLineEntry .flowOut ⟨c::(cs++tail),col⟩ ⟨cs++tail,col+1⟩ :=
   .mk _ _ _ _ (.nil _) (.safe _ c _ _ (letter_grammar hl).1 (letter_facts hl).2.1 (letter_facts hl).1)
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using GStar.cons _ _ _ hstep ht

lemma word_plain (cs tail : List Char) (col n : Nat) (hc : Word cs) :
 SNsPlain n .flowOut ⟨cs++tail,col⟩ ⟨tail,col+cs.length⟩ := by
 cases cs with
 | nil => exact False.elim (hc.1 rfl)
 | cons c cs =>
  have hg := letter_grammar (hc.2 c (by simp))
  have ht := word_tail cs tail (col+1) (fun d hd => hc.2 d (by simp [hd]))
  have hf : SNsPlainFirst .flowOut ⟨c::(cs++tail),col⟩ ⟨cs++tail,col+1⟩ :=
   .nonIndicator _ c _ _ hg.1 hg.2
  have ho := SNsPlainOneLine.mk .flowOut _ _ _ hf ht
  have hm := SNsPlainMultiLine.mk n .flowOut _ _ _ ho (.nil _)
  simpa [SNsPlain,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm

lemma separate_space (tail : List Char) (col n : Nat) :
 SSeparate n .flowOut ⟨' '::tail,col⟩ ⟨tail,col+1⟩ :=
 SSeparateLines.inline n _ _ (.whites _ _ (.mk _ _ _ (.space _ _) (.nil _)))

lemma eof_comments (col : Nat) : SSLComments ⟨[],col⟩ ⟨[],col⟩ :=
 .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

lemma anchor_a (v : List Char) :
 TCNsProperties 1 .flowOut ⟨'&'::'a'::' '::v,2⟩ ⟨' '::v,4⟩ [.defineAnchor "a"] := by
 have ha : SCNsAnchorProperty ⟨'&'::'a'::' '::v,2⟩ ⟨' '::v,4⟩ := by
  refine .mk _ _ _ (.mk _ _ _ (.mk 'a' _ _ (by
   simp [isNsAnchorChar,isNsChar,isLineBreakProp,isLineFeedProp,isCarriageReturnProp,
    isWhiteSpaceProp,isSpaceProp,isTabProp,isPrintableProp,isFlowIndicatorProp])) (.nil _)) ?_
  intro t ht
  cases ht
  rename_i hc
  exact (by simp [isNsAnchorChar,isNsChar,isWhiteSpaceProp,isSpaceProp,isTabProp] : ¬isNsAnchorChar ' ') hc
 have he : TCNsAnchorProperty ⟨'&'::'a'::' '::v,2⟩ ⟨' '::v,4⟩ [.defineAnchor "a"] := by
  refine ⟨ha,?_⟩
  simp [anchorEvents,L4YAML.Proofs.Serialization.TraceOf.span,
   L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool,
   List.takeWhile_cons,isFlowIndicatorBool,isWhiteSpaceBool,isSpaceBool,isTabBool,
   isLineBreakBool,isLineFeedBool,isCarriageReturnBool,isPrintableBool,isPrintableProp]
 simpa using TCNsProperties.anchorFirst (n:=1) (c:=.flowOut) _ _ _ [.defineAnchor "a"] [] he (.none _)

lemma anchored_word_trace (k v : List Char) (hk : Word k) (hv : Word v) :
 TraceOf (AnchoredWordSource.source k v) [.defineAnchor "a"] := by
 let tail := '\n'::':'::' '::suffix v
 have hkey := word_plain k tail 2 1 hk
 have hval := word_plain v [] 5 1 hv
 have hkeycomments : SSLComments ⟨tail,2+k.length⟩ ⟨':'::' '::suffix v,0⟩ :=
  .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _)
 have hkeynode : TBlockIndented 0 .blockOut ⟨' '::(k++tail),1⟩ ⟨':'::' '::suffix v,0⟩ [] :=
  .node _ _ _ _ _ (.flowInBlock 1 .blockOut _ _ _ _ []
   (separate_space (k++tail) 1 1) (.content _ _ _ _ _ (.plain _ _ _ _ hkey)) hkeycomments)
 have hvaluenode : TBlockIndented 0 .blockOut ⟨' '::suffix v,1⟩ ⟨[],5+v.length⟩ [.defineAnchor "a"] := by
  refine .node _ _ _ _ _ (.flowInBlock 1 .blockOut _ _ _ _ _
   (separate_space (suffix v) 1 1) ?_ (eof_comments _))
  simpa [suffix] using TFlowNode.propsContent 1 .flowOut _ _ _ _ [.defineAnchor "a"] []
   (anchor_a v) (separate_space v 4 1) (.plain _ _ _ _ (by simpa using hval))
 have hentry : TBlockMapEntry 0 ⟨'?'::' '::(k++tail),0⟩ ⟨[],5+v.length⟩ [.defineAnchor "a"] := by
  simpa using TBlockMapEntry.explicit 0 _ _ _ _ _ _ [] [.defineAnchor "a"]
   (.mk _ _) hkeynode (.zero _) (.mk _ _) hvaluenode
 have hroot : TBlockNode 0 .blockIn ⟨'?'::' '::(k++tail),0⟩ ⟨[],5+v.length⟩ [.defineAnchor "a"] := by
  simpa using TBlockNode.blockMap 0 .blockIn 0 _ _ _ _ [] [.defineAnchor "a"]
   (.none _) (.startOfLine _ _ (.nil _)) (.single 0 _ _ _ _ (.zero _) hentry)
 refine ⟨5+v.length,?_⟩
 simpa [AnchoredWordSource.source,ExplicitWordFragment.source,tail] using
  TLYamlStream.single _ _ _ _ [.defineAnchor "a"] [] (.nil _)
   (.some _ _ _ (.bare _ _ _ (.mk _ _ _ hroot))) (.nil _)

#print axioms anchored_word_trace
end L4YAML.Tests.Guards.AnchoredWordGrammar
