module
public import Tests.Guards.Proofs.AnchoredWordExecution
public import Tests.Guards.Proofs.ExplicitWordParser
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import all L4YAML.Parser.TokenParser
import all L4YAML.Parser.State
import all L4YAML.Spec.Types
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredWordParser
open L4YAML L4YAML.Scanner L4YAML.TokenParser L4YAML.CharPredicates
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.ExplicitWordExecution (pos)
open L4YAML.Tests.Guards.ExplicitWordParser (scalar_exact parseNodeProperties_skip parseDirectives_skip)
open L4YAML.Tests.Guards.AnchoredWordSource
open L4YAML.Tests.Guards.AnchoredWordExecution
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

-- Blueprint 7.7 fragment: exact raw serialization tree and composed value.
def anchoredValue (v : List Char) : YamlValue :=
 .scalar {content:=String.ofList v,style:=.plain,anchor:=some "a"}
def expected (k v : List Char) : YamlValue :=
 .mapping .block #[(YamlValue.plainScalar (String.ofList k),anchoredValue v)]
def composed (k v : List Char) : YamlValue :=
 .mapping .block #[(YamlValue.plainScalar (String.ofList k),YamlValue.plainScalar (String.ofList v))]
def document (k v : List Char) : YamlDocument :=
 {value:=expected k v,anchors:=#[("a",((anchoredValue v).stripAnchors.adaptForFlowContext).resolveAliases #[])]}
def ps (k v : List Char) (n : Nat) (path : YamlPath := #[]) : ParseState :=
 {tokens:=expectedTokens k v,pos:=n,currentPath:=path}
def psA (k v : List Char) (n : Nat) (path : YamlPath := #[]) : ParseState :=
 ((ps k v n path).declareAnchor "a").addAnchor "a" (anchoredValue v)

lemma word_no_flow (v : List Char) (hv : ∀ c ∈ v, Letter c) : hasFlowIndicator v=false := by
 induction v with
 | nil => rfl
 | cons c cs ih =>
  have hi := (letter_facts (hv c (by simp))).2.2.2.2.2.2.2.2.1
  simp only [isIndicatorBool,decide_eq_false_iff_not,List.mem_cons,List.mem_singleton,not_or] at hi
  have ht := ih (fun d hd => hv d (by simp [hd]))
  simp_all [hasFlowIndicator,beq_iff_eq]

lemma document_word (k v : List Char) (hv : ∀ c ∈ v, Letter c) :
 document k v={value:=expected k v,anchors:=#[("a",YamlValue.plainScalar (String.ofList v))]} := by
 simp [document,anchoredValue,YamlValue.stripAnchors,YamlValue.adaptForFlowContext,
  YamlValue.resolveAliases,YamlValue.plainScalar,word_no_flow v hv]

lemma value_properties (k v : List Char) (path : YamlPath) :
 parseNodeProperties (ps k v 5 path)=
 .ok ({anchor:=some "a"},(ps k v 6 path).declareAnchor "a") := by
 unfold parseNodeProperties
 dsimp only []
 simp [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
  List.range'_succ,List.forIn_cons,List.forIn_nil,
  ps,expectedTokens,ExplicitWordExecution.tok,ParseState.peek?,ParseState.advance,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma value_parse (k v : List Char) (path : YamlPath) (n : Nat) :
 parseNode (ps k v 5 path) (n+1)=.ok (anchoredValue v,psA k v 7 path) := by
 have hp : (ps k v 5 path).peek?=some (.anchor "a") := by
  simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]
 have hs : ((ps k v 6 path).declareAnchor "a").peek?=some (.scalar (String.ofList v) .plain) := by
  simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok,ParseState.declareAnchor]
 have hval : validateNodeProps ((ps k v 6 path).declareAnchor "a") (ps k v 5 path).pos {anchor:=some "a"}=.ok () := by
  simp only [validateNodeProps,hs]
  rfl
 have hcontent : ∀ b, parseNodeContent ((ps k v 6 path).declareAnchor "a") n {anchor:=some "a"} b=
  .ok (anchoredValue v,((ps k v 6 path).declareAnchor "a").advance) := by
  intro b; simp [parseNodeContent,hs,anchoredValue]
 unfold parseNode
 simp only [hp,bind,Except.bind,value_properties]
 rw [hval]
 simp only [bind,Except.bind,hcontent]
 simp [applyNodeFinalization,applyNodeProps,anchoredValue,psA,ps,
  ParseState.advance,ParseState.declareAnchor,ParseState.addAnchor]

lemma key_entry (k v : List Char) (n : Nat) :
 handleBlockMappingKeyEntry (ps k v 2) (n+1) 0=
 .ok (YamlValue.plainScalar (String.ofList k),anchoredValue v,psA k v 7) := by
 have hk := scalar_exact (ps k v 3) n (String.ofList k) .plain
  (by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]) (by rfl)
 have hv := value_parse k v #[.key (String.ofList k)] n
 simp [ps,psA,expectedTokens,pos,ExplicitWordExecution.tok,ParseState.advance] at hk hv
 simp [handleBlockMappingKeyEntry,parseBlockMappingEntryValue,hk,hv,
  ps,psA,expectedTokens,pos,ExplicitWordExecution.tok,YamlValue.plainScalar,
  ParseState.peekPos?,ParseState.peek?,ParseState.advance,ParseState.tryConsume,
  ParseState.declareAnchor,ParseState.addAnchor,anchoredValue,
  Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,List.range'_succ,List.forIn_cons,List.forIn_nil,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma map_body (k v : List Char) (n : Nat) :
 parseBlockMapping (ps k v 1) (n+3)=.ok (expected k v,psA k v 8) := by
 have he := key_entry k v n
 simp [ps,expectedTokens,ExplicitWordExecution.tok] at he
 simp only [parseBlockMapping]
 change (do
  let (pairs,s) ← parseBlockMappingLoop (ps k v 2) (n+2) #[]
  let t := match s.peek? with | some .blockEnd => s.advance | _ => s
  pure (YamlValue.mapping .block pairs,t)) = _
 rw [parseBlockMappingLoop]
 simp only [show (ps k v 2).peek?=some .key by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok],he]
 simp [parseBlockMappingLoop,he,ps,psA,expectedTokens,expected,ParseState.peek?,ParseState.advance,
  ParseState.declareAnchor,ParseState.addAnchor,ExplicitWordExecution.tok,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma root_parse (k v : List Char) (n : Nat) :
 parseNode (ps k v 1) (n+4)=.ok (expected k v,psA k v 8) := by
 have hp : (ps k v 1).peek?=some .blockMappingStart := by
  simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]
 have hprops := parseNodeProperties_skip (ps k v 1) (by rw [hp]; trivial)
 have hval : validateNodeProps (ps k v 1) (ps k v 1).pos {}=.ok () := by
  simp [validateNodeProps,hp,pure,Except.pure]
 have hcontent : ∀ b, parseNodeContent (ps k v 1) (n+3) {} b=.ok (expected k v,psA k v 8) := by
  intro b; simp [parseNodeContent,hp,map_body k v n]
 rw [show n+4=(n+3)+1 by omega]
 unfold parseNode
 simp only [hp,bind,Except.bind,hprops,hval,hcontent]
 simp [applyNodeFinalization,applyNodeProps,expected,psA,ps,ParseState.declareAnchor,ParseState.addAnchor]

lemma prepared (k v : List Char) : prepareDocumentState (ps k v 1)=.ok (#[],ps k v 1) := by
 have hd := parseDirectives_skip (ps k v 1) (by simp [ps,ParseState.peek?,expectedTokens,ExplicitWordExecution.tok])
 rw [prepareDocumentState,hd]
 simp [ps,expectedTokens,ParseState.peek?,ParseState.tryConsume,ExplicitWordExecution.tok,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma parsed_document (k v : List Char) :
 parseDocument (ps k v 1)=.ok (document k v,psA k v 8) := by
 rw [parseDocument,prepared]
 change (do
  let (value,s) ← parseNode (ps k v 1) 40
  pure (({value,anchors:=s.anchors,nodePositions:=s.nodePositions} : YamlDocument),s)) = _
 rw [root_parse k v 36]
 simp [psA,ps,document,ParseState.declareAnchor,ParseState.addAnchor,anchoredValue,YamlValue.plainScalar,
  YamlValue.stripAnchors,YamlValue.adaptForFlowContext,YamlValue.resolveAliasesWith,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma parsed_tokens (k v : List Char) :
 parseStream (expectedTokens k v)=.ok #[document k v] := by
 have hd := parsed_document k v
 have he : ({tokens:=expectedTokens k v} : ParseState).expect .streamStart "STREAM-START"=.ok (ps k v 1) := by
  simp [ParseState.expect,ParseState.peek?,ParseState.advance,expectedTokens,ps,ExplicitWordExecution.tok]
 rw [parseStream,he]
 change parseStreamLoop (ps k v 1) #[] .initial 9 = _
 rw [parseStreamLoop]
 have hp : (ps k v 1).peek?=some .blockMappingStart := by simp [ps,expectedTokens,ParseState.peek?,ExplicitWordExecution.tok]
 simp only [hp,StreamState.validNextToken,Bool.not_true,ite_false]
 rw [hd]
 simp [parseStreamLoop,psA,ps,expectedTokens,ParseState.peek?,ParseState.tryConsume,
  ParseState.declareAnchor,ParseState.addAnchor,ExplicitWordExecution.tok,
  bind,Except.bind,pure,Pure.pure,Except.pure]

lemma parsed_raw_source (k v : List Char) (hk : Word k) (hv : Word v) :
 parseYamlSingleRaw (AnchoredWordSource.source k v)=.ok (document k v) := by
 simp only [parseYamlSingleRaw,parseYamlRaw,anchored_word_filtered k v hk hv,parsed_tokens]
 simp

lemma parsed_source (k v : List Char) (hk : Word k) (hv : Word v) :
 parseYamlSingle (AnchoredWordSource.source k v)=.ok (composed k v) := by
 simp only [parseYamlSingle,parseYaml,parseYamlRaw,anchored_word_filtered k v hk hv,parsed_tokens]
 simp [YamlDocument.compose,document,expected,composed,anchoredValue,YamlValue.plainScalar,
  YamlValue.resolveAliasesOrdered,YamlValue.resolveAliasesOrdered.goPairs,
  YamlValue.stripAnchors,YamlValue.stripAnchors.stripPairs]

#print axioms parsed_tokens
#print axioms parsed_raw_source
#print axioms parsed_source
end L4YAML.Tests.Guards.AnchoredWordParser
