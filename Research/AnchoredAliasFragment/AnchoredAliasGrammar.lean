module
public import Tests.Guards.Proofs.AnchoredAliasSource
public import Tests.Guards.Proofs.AnchoredWordGrammar
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredAliasGrammar
open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.AnchoredWordSource (suffix)
open L4YAML.Tests.Guards.AnchoredWordGrammar
open L4YAML.Tests.Guards.AnchoredAliasSource
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

-- Blueprint 7.7: independently constructed grammar, without scanner admission.
lemma alias_a : TCNsAliasNode ⟨['*','a'],2⟩ ⟨[],4⟩ [.useAlias "a"] := by
 refine ⟨?_,?_⟩
 · refine .mk _ _ _ (.mk _ _ _ (.mk 'a' _ _ (by
    simp [isNsAnchorChar,isNsChar,isLineBreakProp,isLineFeedProp,isCarriageReturnProp,
     isWhiteSpaceProp,isSpaceProp,isTabProp,isPrintableProp,isFlowIndicatorProp])) (.nil _)) ?_
   intro t ht; cases ht
 · simp [aliasEvents,span,L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool,
    isFlowIndicatorBool,isWhiteSpaceBool,isSpaceBool,isTabBool,isLineBreakBool,isLineFeedBool,
    isCarriageReturnBool,isPrintableBool,isPrintableProp]

lemma copy_word : Word ['c','o','p','y'] := by simp [Word,Letter]

lemma alias_word_trace (k v : List Char) (hk : Word k) (hv : Word v) :
 TraceOf (AnchoredAliasSource.source k v) [.defineAnchor "a",.useAlias "a"] := by
 let rem := ['?',' ','c','o','p','y','\n',':',' ','*','a']
 let tail := '\n'::':'::' '::suffix (body v)
 have hkey := word_plain k tail 2 1 hk
 have hval := word_plain v ending 5 1 hv
 have hkeycomments : SSLComments ⟨tail,2+k.length⟩ ⟨':'::' '::suffix (body v),0⟩ :=
  .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _)
 have hvaluecomments : SSLComments ⟨ending,5+v.length⟩ ⟨rem,0⟩ :=
  .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _)
 have hkeynode : TBlockIndented 0 .blockOut ⟨' '::(k++tail),1⟩ ⟨':'::' '::suffix (body v),0⟩ [] :=
  .node _ _ _ _ _ (.flowInBlock 1 .blockOut _ _ _ _ []
   (separate_space (k++tail) 1 1) (.content _ _ _ _ _ (.plain _ _ _ _ hkey)) hkeycomments)
 have hvaluenode : TBlockIndented 0 .blockOut ⟨' '::suffix (body v),1⟩ ⟨rem,0⟩ [.defineAnchor "a"] := by
  refine .node _ _ _ _ _ (.flowInBlock 1 .blockOut _ _ _ _ _
   (separate_space (suffix (body v)) 1 1) ?_ hvaluecomments)
  simpa [suffix,body] using TFlowNode.propsContent 1 .flowOut _ _ _ _ [.defineAnchor "a"] []
   (anchor_a (body v)) (separate_space (body v) 4 1) (.plain _ _ _ _ hval)
 have hentry : TBlockMapEntry 0 ⟨'?'::' '::(k++tail),0⟩ ⟨rem,0⟩ [.defineAnchor "a"] := by
  simpa using TBlockMapEntry.explicit 0 _ _ _ _ _ _ [] [.defineAnchor "a"]
   (.mk _ _) hkeynode (.zero _) (.mk _ _) hvaluenode
 have hcopy := word_plain ['c','o','p','y'] ['\n',':',' ','*','a'] 2 1 copy_word
 have hcopycomments : SSLComments ⟨['\n',':',' ','*','a'],6⟩ ⟨[':',' ','*','a'],0⟩ :=
  .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _)
 have hcopynode : TBlockIndented 0 .blockOut ⟨[' ','c','o','p','y','\n',':',' ','*','a'],1⟩ ⟨[':',' ','*','a'],0⟩ [] :=
  .node _ _ _ _ _ (.flowInBlock 1 .blockOut _ _ _ _ []
   (separate_space _ 1 1) (.content _ _ _ _ _ (.plain _ _ _ _ hcopy)) hcopycomments)
 have haliasnode : TBlockIndented 0 .blockOut ⟨[' ','*','a'],1⟩ ⟨[],4⟩ [.useAlias "a"] :=
  .node _ _ _ _ _ (.flowInBlock 1 .blockOut _ _ _ _ _ (separate_space _ 1 1)
   (.alias _ _ _ _ _ alias_a) (eof_comments _))
 have hsecond : TBlockMapEntry 0 ⟨rem,0⟩ ⟨[],4⟩ [.useAlias "a"] := by
  simpa [rem] using TBlockMapEntry.explicit 0 _ _ _ _ _ _ [] [.useAlias "a"]
   (.mk _ _) hcopynode (.zero _) (.mk _ _) haliasnode
 have hroot : TBlockNode 0 .blockIn ⟨'?'::' '::(k++tail),0⟩ ⟨[],4⟩ [.defineAnchor "a",.useAlias "a"] := by
  simpa using TBlockNode.blockMap 0 .blockIn 0 _ _ _ _ [] [.defineAnchor "a",.useAlias "a"]
   (.none _) (.startOfLine _ _ (.nil _))
   (.cons 0 _ _ _ _ [.defineAnchor "a"] [.useAlias "a"] (.zero _) hentry
    (.single 0 _ _ _ _ (.zero _) hsecond))
 refine ⟨4,?_⟩
 simpa [AnchoredAliasSource.source,AnchoredWordSource.source,ExplicitWordFragment.source,tail] using
  TLYamlStream.single _ _ _ _ [.defineAnchor "a",.useAlias "a"] [] (.nil _)
   (.some _ _ _ (.bare _ _ _ (.mk _ _ _ hroot))) (.nil _)

lemma alias_events_wellformed : SerializationWellFormed [.defineAnchor "a",.useAlias "a"] := by
 simp [SerializationWellFormed,WellFormedFrom,AliasAllowed]

#print axioms alias_word_trace
#print axioms alias_events_wellformed
end L4YAML.Tests.Guards.AnchoredAliasGrammar
