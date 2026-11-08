module

public import FlowTokenBridge
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

#guard (TokenParser.parseYaml "[[\"é\\x01\"]]").isOk
#print axioms nested_scan
#print axioms producer
#print axioms public_accepts

end MathGraph.WholeSource.NestedSourceProducer
