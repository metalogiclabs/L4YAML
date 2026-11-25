module
public import Tests.Guards.Proofs.ExplicitWordExecution
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all L4YAML.Parser.TokenParser
import all L4YAML.Parser.State
import all L4YAML.Spec.Types
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ExplicitWordParser
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Tests.Guards.ExplicitWordFragment L4YAML.Tests.Guards.ExplicitWordExecution
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def expected (k v : List Char) : YamlValue :=
 .mapping .block #[(YamlValue.plainScalar (String.ofList k),YamlValue.plainScalar (String.ofList v))]

lemma parseNodeProperties_skip (ps : ParseState)
    (h : match ps.peek? with
        | some (.anchor _) | some (.tag _ _) => False
        | _ => True) :
    parseNodeProperties ps = .ok ({}, ps) := by
  unfold parseNodeProperties
  dsimp only []
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
             Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
             show List.range' 0 2 1 = 0 :: List.range' 1 1 1 from by decide,
             List.forIn_cons, bind, Except.bind, pure, Except.pure]
  cases hpk : ps.peek?
  case none => simp_all
  case some tok => cases tok <;> simp_all

lemma parseDirectives_skip (ps : ParseState)
    (h : match ps.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True) :
    parseDirectives ps = (#[], ps) := by
  unfold parseDirectives
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize ps.tokens.size - ps.pos = fuel
  cases fuel with
  | zero =>
    simp only [List.range', List.forIn_nil]
    rfl
  | succ n =>
    simp only [List.range'_succ, List.forIn_cons, pure, bind]
    split
    · rename_i minor h_done
      split at h_done
      · cases h_done
      · cases h_done
      · cases h_done; rfl
    · rename_i b h_yield
      split at h_yield
      · exfalso; revert h; simp_all
      · exfalso; revert h; simp_all
      · cases h_yield


def ps (k v : List Char) (n : Nat) (path : YamlPath := #[]) : ParseState :=
 {tokens:=expectedTokens k v,pos:=n,currentPath:=path}

lemma scalar_exact (s : ParseState) (n : Nat) (text : String) (style : ScalarStyle)
 (hp : s.peek? = some (.scalar text style)) (ht : s.trackPositions=false) :
 parseNode s (n+1) = .ok (YamlValue.scalar {content:=text,style},s.advance) := by
 have hprops := parseNodeProperties_skip s (by rw [hp]; trivial)
 have hval : validateNodeProps s s.pos {} = .ok () := by
  simp [validateNodeProps,hp,pure,Except.pure]
 have hcontent : ∀ b, parseNodeContent s n {} b =
  .ok (YamlValue.scalar {content:=text,style},s.advance) := by
  intro b; simp [parseNodeContent,hp]
 unfold parseNode
 simp only [hp,bind,Except.bind,hprops,hval,hcontent]
 simp [applyNodeFinalization,applyNodeProps,ParseState.advance,ht]

lemma key_entry (k v : List Char) (n : Nat) :
 handleBlockMappingKeyEntry (ps k v 2) (n+1) 0 =
 .ok (YamlValue.plainScalar (String.ofList k),YamlValue.plainScalar (String.ofList v),ps k v 6) := by
 have hk := scalar_exact (ps k v 3) n (String.ofList k) .plain
  (by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]) (by rfl)
 have hv := scalar_exact (ps k v 5 #[.key (String.ofList k)]) n (String.ofList v) .plain
  (by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]) (by rfl)
 simp [ps,expectedTokens,pos,ExplicitWordExecution.tok,ParseState.advance] at hk hv
 simp [handleBlockMappingKeyEntry,parseBlockMappingEntryValue,hk,hv,
  ps,expectedTokens,pos,ExplicitWordExecution.tok,YamlValue.plainScalar,
  ParseState.peekPos?,ParseState.peek?,ParseState.advance,ParseState.tryConsume,
  Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,List.range'_succ,List.forIn_cons,List.forIn_nil,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma map_body (k v : List Char) (n : Nat) :
 parseBlockMapping (ps k v 1) (n+3) = .ok (expected k v,ps k v 7) := by
 have he := key_entry k v n
 simp [ps,expectedTokens,ExplicitWordExecution.tok] at he
 simp only [parseBlockMapping]
 change (do
  let (pairs,s) ← parseBlockMappingLoop (ps k v 2) (n+2) #[]
  let t := match s.peek? with | some .blockEnd => s.advance | _ => s
  pure (YamlValue.mapping .block pairs,t)) = _
 rw [parseBlockMappingLoop]
 simp only [show (ps k v 2).peek?=some .key by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok],he]
 simp [parseBlockMappingLoop,he,ps,expectedTokens,expected,ParseState.peek?,ParseState.advance,ExplicitWordExecution.tok,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma root_parse (k v : List Char) (n : Nat) :
 parseNode (ps k v 1) (n+4) = .ok (expected k v,ps k v 7) := by
 have hp : (ps k v 1).peek?=some .blockMappingStart := by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]
 have hprops := parseNodeProperties_skip (ps k v 1) (by rw [hp]; trivial)
 have hval : validateNodeProps (ps k v 1) (ps k v 1).pos {} = .ok () := by
  simp [validateNodeProps,hp,pure,Except.pure]
 have hcontent : ∀ b, parseNodeContent (ps k v 1) (n+3) {} b =
  .ok (expected k v,ps k v 7) := by intro b; simp [parseNodeContent,hp,map_body k v n]
 rw [show n+4=(n+3)+1 by omega]
 unfold parseNode
 simp only [hp,bind,Except.bind,hprops,hval,hcontent]
 simp [applyNodeFinalization,applyNodeProps,expected,ps]

lemma prepared (k v : List Char) : prepareDocumentState (ps k v 1) = .ok (#[],ps k v 1) := by
 have hd := parseDirectives_skip (ps k v 1) (by simp [ps,ParseState.peek?,expectedTokens,ExplicitWordExecution.tok])
 rw [prepareDocumentState,hd]
 simp [ps,expectedTokens,ParseState.peek?,ParseState.tryConsume,ExplicitWordExecution.tok,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma parsed_document (k v : List Char) :
 parseDocument (ps k v 1) = .ok ({value:=expected k v},ps k v 7) := by
 rw [parseDocument,prepared]
 change (do
  let (value,s) ← parseNode (ps k v 1) 36
  pure (({value,anchors:=s.anchors,nodePositions:=s.nodePositions} : YamlDocument),s)) = _
 rw [root_parse k v 32]
 simp [ps,bind,Except.bind,pure,Pure.pure,Except.pure]

lemma parsed_tokens (k v : List Char) :
 parseStream (expectedTokens k v) = .ok #[{value:=expected k v}] := by
 have hd := parsed_document k v
 have he : ({tokens:=expectedTokens k v} : ParseState).expect .streamStart "STREAM-START" = .ok (ps k v 1) := by
  simp [ParseState.expect,ParseState.peek?,ParseState.advance,expectedTokens,ps,ExplicitWordExecution.tok]
 rw [parseStream,he]
 change parseStreamLoop (ps k v 1) #[] .initial 8 = _
 rw [parseStreamLoop]
 have hp : (ps k v 1).peek?=some .blockMappingStart := by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]
 simp only [hp,StreamState.validNextToken,Bool.not_true,ite_false]
 rw [hd]
 simp [parseStreamLoop,ps,expectedTokens,ParseState.peek?,ParseState.tryConsume,ExplicitWordExecution.tok,
  bind,Except.bind,pure,Pure.pure,Except.pure]


lemma parsed_source (k v : List Char) (hk : Word k) (hv : Word v) :
 parseYamlSingle (source k v) = .ok (expected k v) := by
 have hscan : scanFiltered (source k v) = .ok (expectedTokens k v) := by
  cases k with
  | nil => exact False.elim (hk.1 rfl)
  | cons c ks =>
   cases v with
   | nil => exact False.elim (hv.1 rfl)
   | cons d vs => rw [scan_filtered c d ks vs hk.2 hv.2,filtered_shape]
 simp only [parseYamlSingle,parseYaml,parseYamlRaw,hscan,parsed_tokens]
 simp [YamlDocument.compose,expected,YamlValue.plainScalar,YamlValue.resolveAliasesOrdered,
  YamlValue.resolveAliasesOrdered.goPairs,YamlValue.stripAnchors,YamlValue.stripAnchors.stripPairs]

#print axioms parsed_tokens
#print axioms parsed_source
end L4YAML.Tests.Guards.ExplicitWordParser
