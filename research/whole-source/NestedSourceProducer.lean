module

public import FlowQuotedEntries
public import SourceBridge
public import QuotedPair
import all L4YAML.Proofs.Serialization.TokenEvents

/-! A source-only nested sequence slice, from the actual scanner through
both parser premises to public acceptance. -/

@[expose] public section
namespace MathGraph.WholeSource.NestedSourceProducer

open L4YAML Scanner Surface
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.EmitterScannability L4YAML.Proofs.TokenGrammar
open L4YAML.Research.AcceptedSource
open MathGraph.WholeSource.FlowTokenBridge
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvent)
open L4YAML.Proofs.ScalarCoupling

def Language (input : String) : Prop :=
  ∃ body col, input.toList = '[' :: '[' :: body ∧
    SCDoubleQuotedOk ⟨body, 2⟩ ⟨[']', ']'], col⟩

def values (text : String) : List YamlToken :=
  [.streamStart, .flowSequenceStart, .flowSequenceStart, .scalar text .doubleQuoted,
   .flowSequenceEnd, .flowSequenceEnd, .streamEnd]

private def filtered (s : ScannerState) := (s.tokens.filter (fun t => t.val != .placeholder)).map (·.val)

lemma nested_scan (input : String) (h : Language input) :
    ∃ ts text, Scanner.scanFiltered input = .ok ts ∧ ts.toList.map (·.val) = values text := by
  obtain ⟨body, col, hStart, hQuote⟩ := h
  let init := (ScannerState.mk' input).emit .streamStart
  obtain ⟨outer, ho, hco, hlo, hdo, hio, hcolo, hfo, hindo, _, hlineo, hAllo, hEndo,
    _, hto, _, _, _, hLasto, hKindo⟩ := scanNextToken_flow_open_init input ('[' :: body) hStart
  obtain ⟨inner, hi, hci, hli, hdi, hii, _, hcoli, hLinei, hAlli, hEndi, hStackLine,
    _, _, _, _, hLasti, hKindPush, _⟩ :=
    scanNextToken_flow_open_nested outer body hco hfo hindo (by omega)
      (by rwa [hlineo]) hEndo hdo hLasto
  obtain ⟨tokOpen, hTokOpen, hPushOpen⟩ :=
    scanNextToken_flow_open_seq_filtered_push outer body hco hfo hindo (by omega) hi
  have hfi : inner.inFlow = true := by simp [ScannerState.inFlow, hli, hlo]
  have hindi : inner.currentIndent < 0 := by simpa only [ScannerState.currentIndent, hii] using hindo
  have hCol2 : inner.col = 2 := by omega
  obtain ⟨rest, hRest⟩ := source_quoted_opening hQuote
  change body = '"' :: rest at hRest
  subst body
  obtain ⟨child, text, hq, hcq, hlq, hdq, hiq, _, hcolq, _, _, hLineq, hAllq, _, hKeyq, htq⟩ :=
    source_dq_flow_dispatch inner rest _ hci (hCol2.symm ▸ hQuote) hfi hindi
      (by omega) hAlli hEndi (hdi.trans hdo) hLasti
  have hfq : child.inFlow = true := by simp [ScannerState.inFlow, hlq, hli, hlo]
  have hindq : child.currentIndent < 0 := by simpa only [ScannerState.currentIndent, hiq] using hindi
  have hKindq : child.flowStack.back? = some true := by
    rw [source_flow_stack_of_level hq hlq, hKindPush]
    simp
  have hCorrq : ScannerSurfCorr child ⟨[']', ']'], child.col⟩ := hcq.col_eq ▸ hcq
  have hStackq : StackEndLineOnLine child child.line := by
    simpa only [StackEndLineOnLine, hKeyq, hLineq] using hStackLine
  obtain ⟨closed, hc, hcc, hlc, hdc, hic, _, hColc, _⟩ :=
    scanNextToken_flow_close_seq_nested child [']'] hCorrq hfq hindq hcolq
      (by omega) hAllq hStackq (hdq.trans (hdi.trans hdo)) hKindq
  obtain ⟨tokClose, hTokClose, hPushClose⟩ :=
    scanNextToken_flow_close_seq_filtered_push child [']'] hCorrq hfq hindq hcolq
      (by omega) hKindq hc
  have hKindc : closed.flowStack.back? = some true := by
    rcases scanNextToken_flowStack_step hc with he | he | he | ⟨_, _, hpop⟩
    · omega
    · omega
    · omega
    · rw [hpop, source_flow_stack_of_level hq hlq, hKindPush]
      simpa using hKindo
  have hfC : closed.inFlow = true := by simp [ScannerState.inFlow, hlc, hlq, hli, hlo]
  have hindC : closed.currentIndent < 0 := by simpa only [ScannerState.currentIndent, hic] using hindq
  have hIdC : closed.indents = #[{column := -1, isSequence := false}] := by
    rw [hic, hiq, hii, hio]
    rfl
  have hDPC : closed.directivesPresent = false := hdc.trans (hdq.trans (hdi.trans hdo))
  have hLevelC : closed.flowLevel = 1 := by omega
  have hVals : filtered closed =
      #[.streamStart, .flowSequenceStart, .flowSequenceStart, .scalar text .doubleQuoted,
        .flowSequenceEnd] := by
    unfold filtered
    rw [hPushClose, Array.map_push, hTokClose, htq, hPushOpen, Array.map_push, hTokOpen, hto]
    rfl
  obtain ⟨final, hz, hfz, hdz, hpz, hiz, tokLast, hTokLast, hPushLast⟩ :=
    scanNextToken_flow_close_seq_outermost_ext closed hcc hfC hindC (by omega) hLevelC hDPC hKindc
  obtain ⟨checked, hz', _, _, _, hDangling, hIndent⟩ :=
    scanNextToken_flow_close_seq_outermost closed hcc hfC hindC (by omega) hLevelC hDPC hKindc hIdC
      (no_props_of_filtered_pin hVals (by
        intro v hv
        simp [Array.mem_def] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl <;> rfl))
  have hSame : checked = final := Option.some.inj (Except.ok.inj (hz'.symm.trans hz))
  subst checked
  have hEOF := scanNextToken_eof final hpz
  have hChain : ScanChain init 5 final :=
    .step ho (.step hi (.step hq (.step hc (.single hz))))
  have hNoBOM : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have hSource := initial_corr input input.toList (chars_from_zero_toList input)
    rw [hStart] at hSource
    rw [(peek_of_corr hSource).1]
    decide
  have hScan := scanFiltered_tokens_eq_of_chain_short_stack input _ final 5 rfl hNoBOM
    hChain hEOF hfz hdz hDangling hIndent (ScanChain.fuel_bound _ _ _ _ rfl hChain hEOF)
    (by rw [hiz, hIdC]; decide)
  refine ⟨_, text, hScan, ?_⟩
  have hEnd : (final.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
      (final.tokens.filter (fun t => t.val != .placeholder)).push
        {pos := final.currentPos, val := .streamEnd} := by
    rw [show (final.emit .streamEnd).tokens =
      final.tokens.push {pos := final.currentPos, val := .streamEnd} from rfl, Array.filter_push]
    rfl
  unfold filtered at hVals
  -- The stream-end token is supplied by the actual scanner wrapper.
  rw [hEnd, ← Array.toList_map, Array.map_push, hPushLast, Array.map_push, hTokLast]
  rw [show (closed.tokens.filter (fun t => t.val != .placeholder)).map (·.val) = _ from hVals]
  rfl

lemma nested_token_conditions (ts : Toks) (text : String)
    (hVals : ts.toList.map (·.val) = values text) : TokenGrammar ts ∧ TokenStateOk ts := by
  have ht (i : Nat) : tok ts i = (values text)[i]? := by
    unfold tok
    rw [← hVals, List.getElem?_map, ← Array.getElem?_toList]
  have hSize : ts.size = 7 := by
    have hs := congrArg List.length hVals
    simpa [values] using hs
  have inner : Shape ts .node 2 5 :=
    .seq (ht 2) (.first (.scalar (ht 3)) (.done (ht 4))) (ht 4)
  have outer : Shape ts .node 1 6 :=
    .seq (ht 1) (.first inner (.done (ht 5))) (ht 5)
  refine ⟨single_document_grammar (ht 0) outer (ht 6) hSize.symm, quiet_values_state hVals ?_⟩
  intro t ht
  simp [values] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [Quiet, tokenEvent]

lemma producer : MathGraph.WholeSource.SourceBridge.Obligation Language := by
  intro input h
  obtain ⟨ts, text, hs, hv⟩ := nested_scan input h
  obtain ⟨hg, hw⟩ := nested_token_conditions ts text hv
  exact ⟨ts, hs, hg, hw⟩

lemma public_accepts (input : String) (h : Language input) :
    ∃ docs, TokenParser.parseYaml input = .ok docs :=
  MathGraph.WholeSource.SourceBridge.accepts_of_producer producer input h

open MathGraph.WholeSource.FlowCloseLanding MathGraph.WholeSource.FlowQuotedEntries

/-- A compact outer sequence containing one inner sequence whose scalar
entries, separators, and optional trailing comma are specified by source rules. -/
def SequenceListLanguage (allowPlain : Bool) (input : String) : Prop :=
  ∃ body col n trailing, input.toList = '[' :: '[' :: body ∧
    QuotedEntries [']'] col allowPlain n trailing ⟨body, 2⟩

abbrev QuotedListLanguage := SequenceListLanguage false
abbrev MixedListLanguage := SequenceListLanguage true

private lemma body_no_props {allowPlain : Bool} {body : List YamlToken} (hImage : ScalarBodyImage allowPlain body) :
    ∀ v ∈ body, v.isNodeProperty = false := by
  induction hImage with
  | empty => simp
  | single value => simp [YamlToken.isNodeProperty]
  | more value _ _ ih =>
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · rfl
    · rfl
    · exact ih v hv

lemma nested_sequence_list_scan {allowPlain : Bool} (input : String)
    (h : SequenceListLanguage allowPlain input) :
    ∃ ts body, Scanner.scanFiltered input = .ok ts ∧ ScalarBodyImage allowPlain body ∧
      ts.toList.map (·.val) = [.streamStart, .flowSequenceStart, .flowSequenceStart] ++
        body ++ [.flowSequenceEnd, .flowSequenceEnd, .streamEnd] := by
  obtain ⟨source, col, n, trailing, hStart, hEntries⟩ := h
  let init := (ScannerState.mk' input).emit .streamStart
  obtain ⟨outer, ho, hco, hlo, hdo, hio, hcolo, hfo, hindo, _, hlineo, hAllo, hEndo,
    _, hto, _, _, _, hLasto, hKindo⟩ := scanNextToken_flow_open_init input ('[' :: source) hStart
  have hOuterValues : filteredValues outer.tokens = [.streamStart, .flowSequenceStart] := by
    unfold filteredValues
    rw [← Array.toList_map, hto]
  obtain ⟨closed, hc, hcc, hlc, _, _, hStack, hIndents, hDP, body, hImage, hValues⟩ :=
    nested_sequence_quoted_entries outer source [']'] col n trailing hco
      (by simpa only [hcolo] using hEntries) (by omega) hindo (by omega)
      (by rwa [hlineo]) hEndo hdo hLasto
  have hfC : closed.inFlow = true := by simpa only [ScannerState.inFlow, hlc] using hfo
  have hKindC := hStack.symm ▸ hKindo
  have hindC : closed.currentIndent < 0 := by simpa only [ScannerState.currentIndent, hIndents] using hindo
  have hIdC : closed.indents = #[{column := -1, isSequence := false}] := hIndents.trans hio
  have hLevelC : closed.flowLevel = 1 := hlc.trans hlo
  have hColEq : closed.col = col + 1 := hcc.col_eq.symm
  have hColC : closed.col > 0 := by omega
  have hClosedSource : ScannerSurfCorr closed ⟨[']'], closed.col⟩ := hColEq.symm ▸ hcc
  obtain ⟨final, hz, hfz, hdz, hpz, hiz, tokLast, hTokLast, hPushLast⟩ :=
    scanNextToken_flow_close_seq_outermost_ext closed hClosedSource hfC hindC hColC hLevelC hDP hKindC
  obtain ⟨checked, hz', _, _, _, hDangling, hIndent⟩ :=
    scanNextToken_flow_close_seq_outermost closed hClosedSource hfC hindC hColC hLevelC hDP hKindC hIdC
      (no_props_of_filtered_pin_list hValues (by
        intro v hv
        rw [hOuterValues] at hv
        simp at hv
        rcases hv with rfl | rfl | hv | rfl
        all_goals first | rfl | exact body_no_props hImage _ hv))
  have hSame : checked = final := Option.some.inj (Except.ok.inj (hz'.symm.trans hz))
  subst checked
  have hEOF := scanNextToken_eof final hpz
  have hChain := (ScanChain.single ho).trans (hc.trans (ScanChain.single hz))
  have hNoBOM : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have hSource := initial_corr input input.toList (chars_from_zero_toList input)
    rw [hStart] at hSource
    rw [(peek_of_corr hSource).1]
    decide
  have hScan := scanFiltered_tokens_eq_of_chain_short_stack input _ final _ rfl hNoBOM
    hChain hEOF hfz hdz hDangling hIndent (ScanChain.fuel_bound _ _ _ _ rfl hChain hEOF)
    (by rw [hiz, hIdC]; decide)
  refine ⟨_, body, hScan, hImage, ?_⟩
  change filteredValues (final.emit .streamEnd).tokens = _
  rw [show (final.emit .streamEnd).tokens =
    final.tokens.push ⟨final.currentPos, .streamEnd, final.currentPos⟩ from rfl,
    filteredValues_push _ _ (by simp)]
  have hFinalValues : filteredValues final.tokens = filteredValues closed.tokens ++ [.flowSequenceEnd] := by
    unfold filteredValues
    simp [hPushLast, hTokLast]
  simp [hFinalValues, hValues, hOuterValues, List.append_assoc]

lemma sequence_list_producer (allowPlain : Bool) :
    MathGraph.WholeSource.SourceBridge.Obligation (SequenceListLanguage allowPlain) := by
  intro input h
  obtain ⟨ts, _, hs, image, hv⟩ := nested_sequence_list_scan input h
  obtain ⟨hg, hw⟩ := nested_quoted_token_conditions image hv
  exact ⟨ts, hs, hg, hw⟩

lemma nested_quoted_list_scan (input : String) (h : QuotedListLanguage input) :
    ∃ ts body, Scanner.scanFiltered input = .ok ts ∧ QuotedBodyImage body ∧
      ts.toList.map (·.val) = [.streamStart, .flowSequenceStart, .flowSequenceStart] ++
        body ++ [.flowSequenceEnd, .flowSequenceEnd, .streamEnd] :=
  nested_sequence_list_scan input h

lemma quoted_list_producer : MathGraph.WholeSource.SourceBridge.Obligation QuotedListLanguage :=
  sequence_list_producer false

/-- Arbitrarily many comma-terminated one-line plain entries may precede
or interleave with the double-quoted entries in the inner sequence. -/
lemma mixed_list_public_accepts (input : String) (h : MixedListLanguage input) :
    ∃ docs, TokenParser.parseYaml input = .ok docs :=
  MathGraph.WholeSource.SourceBridge.accepts_of_producer (sequence_list_producer true) input h

lemma mixed_list_witness : MixedListLanguage "[[a,\"\"]]" := by
  refine ⟨['a', ',', '"', '"', ']', ']'], 6, 2, false, rfl, ?_⟩
  refine .plainMore (col := 2) (commaCol := 3) (contentEnd := ⟨[',', '"', '"', ']', ']'], 3⟩)
    rfl (by decide) (by decide) ?_ (.nil _) ?_
  · exact .mk _ _ _ _ (.nonIndicator _ _ _ _ (by unfold isNsPlainSafe isNsChar; decide)
      (by decide)) (.nil _)
  · exact .single (.inline (.nil _)) (.mk _ _ _ _ (.mk _ _) (.nil _) (.mk _ _))
      (.inline (.nil _))

lemma quoted_list_public_accepts (input : String) (h : QuotedListLanguage input) :
    ∃ docs, TokenParser.parseYaml input = .ok docs :=
  MathGraph.WholeSource.SourceBridge.accepts_of_producer quoted_list_producer input h

#guard (TokenParser.parseYaml "[[ # before first\r\n\"a\" # first\r\n, \"b\", # trailing\n ]]").isOk
#guard (TokenParser.parseYaml "[[ # empty\r\n ]]").isOk
#guard match Scanner.scanFiltered "[[,]]" with
  | .error (.invalidFlowEntry _ _) => true
  | _ => false
#guard (TokenParser.parseYaml "[[a,\"\"]]").isOk
#guard (TokenParser.parseYaml "[[a:b,\"q\",x#y ,\"r\",]]").isOk
#check mixed_list_public_accepts
#print axioms mixed_list_witness
#print axioms mixed_list_public_accepts
#check quoted_list_public_accepts
#print axioms nested_quoted_list_scan
#print axioms quoted_list_producer
#print axioms quoted_list_public_accepts

#guard (TokenParser.parseYaml "[[\"é\\x01\"]]").isOk
#print axioms nested_scan
#print axioms producer
#print axioms public_accepts

end MathGraph.WholeSource.NestedSourceProducer
