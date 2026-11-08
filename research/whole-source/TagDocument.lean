module
public import DirectiveRecordBridge
public import DirectiveEOF
public meta import Lean

/-! Composition on the actual scanner and original fuel. A source TAG directive
is followed by an explicit document marker; an arbitrary body suffix remains
connected to the post-marker scanner state. Empty-body specialization closes
scanFiltered through EOF with its exact token image. This does not prove full
YAML completeness or nonempty-body parsing. -/
@[expose] public section
namespace MathGraph.WholeSource.TagDocument
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.EmitterScannability
open MathGraph.WholeSource.DirectiveBridge
open MathGraph.WholeSource.DirectiveStep
open MathGraph.WholeSource.DirectiveEntry
open MathGraph.WholeSource.DirectiveEOF
open MathGraph.WholeSource.DirectiveRecordBridge

lemma tag_scan_continuation (input : String) (handle pfx rest : List Char) (col : Nat)
    (h : TagDirective handle pfx ⟨input.toList, 0⟩
      ⟨'\n' :: '-' :: '-' :: '-' :: '\n' :: rest, col⟩) :
    ∃ out, scan input = scanLoop out ((input.utf8ByteSize + 1) * 4 - 2) ∧
      ScannerSurfCorr out ⟨'\n' :: rest, 3⟩ ∧ out.flowLevel = 0 ∧
      out.indents = #[{column := -1, isSequence := false}] ∧
      trailingNodeRun? out.tokens = none ∧ out.directivesPresent = false ∧
      (out.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
        #[.streamStart, .tagDirective (String.ofList handle) (String.ofList pfx), .documentStart] := by
  let ready := saveSimpleKey { (ScannerState.mk' input).emit .streamStart with needIndentCheck := false }
  obtain ⟨mid, hfirst, hc, _he, ht, hf, hi⟩ := original_dispatch_record_agreement input h
  have hn : trailingNodeRun? mid.tokens = none := by
    rw [ht]
    exact trailingNodeRun?_push_none ready.tokens _ rfl rfl rfl rfl
  obtain ⟨out, hsecond, hout, hfo, hio, hrun, hdp, _ha, _hs, hvals⟩ :=
    full_step_after_clean_state mid rest col hc hf hi hn
  have hmidValues : (mid.tokens.filter (fun t => t.val != .placeholder)).map (·.val) =
      #[.streamStart, .tagDirective (String.ofList handle) (String.ofList pfx)] := by
    rw [ht, Array.filter_push]
    simp [saveSimpleKey_filter_placeholder,
      ScannerState.emit, ScannerState.mk']
  have hp : input.toList = '%' :: h.afterPercent.chars := percent_source h.percent
  refine ⟨out, scan_eq_after_two input _ mid out hp hfirst hsecond,
    hout, hfo, hio, hrun, hdp, ?_⟩
  rw [hvals, hmidValues]
  rfl

/-- Whole-source scanner completion, with no scanner-success assumption and
without increasing production fuel. The independent grammar is TagDirective
ending exactly before LF/---/LF/EOF. -/
lemma tag_empty_document_scans (input : String) (handle pfx : List Char) (col : Nat)
    (h : TagDirective handle pfx ⟨input.toList, 0⟩ ⟨['\n', '-', '-', '-', '\n'], col⟩) :
    ∃ ts, Scanner.scanFiltered input = .ok ts ∧
      ts.map (·.val) = #[.streamStart,
        .tagDirective (String.ofList handle) (String.ofList pfx), .documentStart, .streamEnd] := by
  obtain ⟨out, hscan, hc, hf, hi, hrun, hd, hvals⟩ :=
    tag_scan_continuation input handle pfx [] col h
  have heof := scanNextToken_after_final_lf out hc hf
  obtain ⟨hdn, hfv⟩ := clean_terminal_checks out hrun
  have hfuel : (input.utf8ByteSize + 1) * 4 - 2 ≥ 1 := by omega
  have hloop := scanLoop_eof_eq hfuel heof hf hd hdn hfv
  have hraw : Scanner.scan input = .ok ((unwindIndents out (-1)).emit .streamEnd).tokens := by
    rw [hscan]
    exact hloop
  have hunwind : unwindIndents out (-1) = out := by
    simp [unwindIndents, hi, unwindIndentsLoop]
  refine ⟨((unwindIndents out (-1)).emit .streamEnd).tokens.filter
    (fun t => t.val != .placeholder), ?_, ?_⟩
  · simp [Scanner.scanFiltered, hraw]
  · rw [hunwind]
    simp [ScannerState.emit, Array.filter_push, Array.map_push, hvals]

#check tag_scan_continuation
#check tag_empty_document_scans
open Lean Elab Command in
run_cmd do
  for n in [``full_step_after_clean_landing, ``full_step_after_clean_state,
      ``tag_scan_continuation, ``tag_empty_document_scans] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"TAG_DOCUMENT_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.TagDocument
