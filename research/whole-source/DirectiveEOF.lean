module
public import DirectiveEntry
public meta import L4YAML.Parser.Composition

/-!
# Source-aware empty-document scanner completion

Group 7.7 dependency: independent `%YAML` source spelling → original scanner
steps → exact post-marker source and terminal checks → `scan`/`scanFiltered`.
Parser acceptance and general grammar completeness are separate obligations.
-/
namespace MathGraph.WholeSource.DirectiveEOF
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.Acceptance
open MathGraph.WholeSource.DirectiveStep MathGraph.WholeSource.DirectiveEntry

private def scanAccepts (input : String) : Bool :=
  (Scanner.scanFiltered input).toOption.isSome
private def parseAccepts (input : String) : Bool :=
  (L4YAML.TokenParser.parseYaml input).toOption.isSome

-- The test matrix exercises the actual entry points, including a multibyte
-- comment, whitespace-only empty documents, and malformed marker controls.
#guard scanAccepts "%YAML 1.2 #\n---\n" = true
#guard scanAccepts "%YAML 1.2 # café\n---\n" = true
#guard parseAccepts "%YAML 1.2 #\n---\n" = true
#guard parseAccepts "%YAML 1.2 # café\n---\n" = true
#guard scanAccepts "%YAML 1.2 #x\n---x" = false
#guard scanAccepts "%YAML 1.2 #x\n ---\n" = false
#guard scanAccepts "%YAML 1.2 #x\nvalue" = false
#guard scanAccepts "%YAML 1.2 #x\n%YAML 1.2\n---\n" = false

/-- At EOF, one final whitespace-loop iteration is a no-op, regardless of
whether `needIndentCheck` is still set. -/
lemma skipToContentLoop_eof_one (s : ScannerState)
    (hpeek : s.peek? = none) : skipToContentLoop s 1 = .ok s := by
  have hnot : ¬ s.offset < s.inputEnd := by
    intro hlt
    have hn : s.peek? ≠ none := by simp [ScannerState.peek?, hlt]
    exact hn hpeek
  have hzero : s.inputEnd - s.offset = 0 := by omega
  have hspaces : skipSpaces s = s := by
    unfold skipSpaces
    rw [hzero]
    unfold skipSpacesLoop
    rfl
  have hwhite : skipWhitespace s = s := by
    unfold skipWhitespace
    rw [hzero]
    unfold skipWhitespaceLoop
    rfl
  have hws : skipToContentWs s = .ok s := by
    unfold skipToContentWs
    split
    · simp [hspaces, hwhite, hpeek]
    · simp [hwhite]
  simp [skipToContentLoop, hws, skipToContentComment, hpeek]

/-- An actual scanner state with precisely one terminal LF in its independently
derived source position ends on the next scan call. This is **not** inferred
from a successful `scan`, and its input budget is not increased. -/
lemma scanNextToken_after_final_lf (s : ScannerState)
    (hc : ScannerSurfCorr s ⟨['\n'], 3⟩)
    (hf : s.flowLevel = 0) : scanNextToken s = .ok none := by
  obtain ⟨hpeek, hmore⟩ := peek_of_corr hc
  obtain ⟨pre, hsplit, hoff⟩ := hc.input_prefix
  have hlfbyte : ('\n' : Char).utf8Size = 1 := by decide
  have hend : s.inputEnd = listByteSize pre + 1 := by
    rw [hc.end_eq, utf8ByteSize_eq_listByteSize, hsplit, listByteSize_append]
    simp [listByteSize, hlfbyte]
  have hrem : s.inputEnd - s.offset + 1 = 2 := by omega
  have hws := ws_noop_nonwhite s '\n' hpeek
    (by decide) (by decide) (by decide) hmore
  have hcEnd : ScannerSurfCorr (consumeNewline s) ⟨[], 0⟩ :=
    (consumeNewline_accepts s (.lf _ 3) hc).1
  let final := {consumeNewline s with simpleKeyAllowed := true}
  have hcFinal : ScannerSurfCorr final ⟨[], 0⟩ :=
    ⟨hcEnd.chars_from, hcEnd.col_eq, hcEnd.end_eq,
      hcEnd.input_prefix, hcEnd.indent_cols_nonneg⟩
  have hpeekFinal : final.peek? = none :=
    peek_none_of_empty_surf final 0 hcFinal
  have hdone := skipToContentLoop_eof_one final hpeekFinal
  have hflow : (consumeNewline s).inFlow = false := by
    have hfEnd := (L4YAML.Proofs.ScannerCorrectness.consumeNewline_preserves_flowLevel s).trans hf
    simp [ScannerState.inFlow, hfEnd]
  have hskip : skipToContent s = .ok final := by
    unfold skipToContent
    rw [hrem]
    rw [skipToContentLoop]
    simpa [hws, skipToContentComment, hpeek, isLineBreakBool,
      isLineFeedBool, isCarriageReturnBool,
      hflow, final] using hdone
  have hnotFinal : ¬ final.offset < final.inputEnd := by
    intro hlt
    have hn : final.peek? ≠ none := by simp [ScannerState.peek?, hlt]
    exact hn hpeekFinal
  have hmFinal : final.hasMore = false := by
    simp [ScannerState.hasMore, hnotFinal]
  have hpre : scanNextToken_preprocess s = .ok none := by
    simp [scanNextToken_preprocess, hskip, hmFinal,
      bind, Except.bind, pure, Except.pure]
  simp [scanNextToken, hpre, bind, Except.bind, pure, Except.pure]

/-- The *same* incoming state used by `scanLoop` passes both terminal safety
checks when it has no unfinished trailing node run. -/
lemma clean_terminal_checks (s : ScannerState)
    (hrun : trailingNodeRun? s.tokens = none) :
    scanLoop_checkDanglingNode s = .ok () ∧
    scanLoop_checkFlowValueIndent s = .ok () :=
  ⟨scanLoop_checkDanglingNode_ok_of_no_run s hrun,
    scanLoop_checkFlowValueIndent_ok_of_no_run s hrun⟩

/-- A positive, independently spelled source family reaches the real scanner's
EOF arm under its **original** fuel budget, emits `streamEnd` and survives
public placeholder filtering. The parser is not an assumption or a conclusion. -/
lemma original_empty_document_scans (input : String)
    (major minor comment : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c)
    (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ [])
    (hcomment : ∀ c ∈ comment, c ≠ '\n' ∧ c ≠ '\r')
    (hsource : input.toList = '%' :: 'Y' :: 'A' :: 'M' :: 'L' :: ' ' ::
      (major ++ '.' :: (minor ++ ' ' :: '#' :: (comment ++ ['\n', '-', '-', '-', '\n'])))) :
    ∃ raw filtered,
      Scanner.scan input = .ok raw ∧
      Scanner.scanFiltered input = .ok filtered ∧
      filtered = raw.filter (fun t => t.val != .placeholder) ∧
      filtered.map (·.val) =
        #[.streamStart, .versionDirective (String.ofList major).toNat!
          (String.ofList minor).toNat!, .documentStart, .streamEnd] := by
  obtain ⟨out, hscan, hc, hf, hi, hrun, hd, _ha, _hs, hvals⟩ :=
    original_scan_continuation_state input major minor comment []
      hma hmi hneMa hneMi hcomment hsource
  have heof := scanNextToken_after_final_lf out hc hf
  obtain ⟨hdn, hfv⟩ := clean_terminal_checks out hrun
  have hfuel : (input.utf8ByteSize + 1) * 4 - 2 ≥ 1 := by omega
  have hloop := scanLoop_eof_eq hfuel heof hf hd hdn hfv
  have hraw : Scanner.scan input =
      .ok ((unwindIndents out (-1)).emit .streamEnd).tokens := by
    rw [hscan]
    exact hloop
  have hunwind : unwindIndents out (-1) = out := by
    simp [unwindIndents, hi, unwindIndentsLoop]
  have hvalEnd :
      ((((unwindIndents out (-1)).emit .streamEnd).tokens.filter
        (fun t => t.val != .placeholder)).map (·.val)) =
          #[.streamStart, .versionDirective (String.ofList major).toNat!
            (String.ofList minor).toNat!, .documentStart, .streamEnd] := by
    rw [hunwind]
    simp [ScannerState.emit, Array.filter_push, Array.map_push, hvals]
  refine ⟨_, _, hraw, ?_, rfl, hvalEnd⟩
  simp [Scanner.scanFiltered, hraw]

#print axioms skipToContentLoop_eof_one
#print axioms scanNextToken_after_final_lf
#print axioms clean_terminal_checks
#print axioms original_empty_document_scans
end
end MathGraph.WholeSource.DirectiveEOF
