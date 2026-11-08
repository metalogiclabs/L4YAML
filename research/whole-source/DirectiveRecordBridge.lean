module
public import DirectiveRecords
public import DirectiveBridge
public import DirectiveEntry
public meta import Lean

/-! General retained-record / scanner-token agreement, not full stream success.
Covers every independent TagDirective, including arbitrary horizontal separators,
primary/secondary/named handles, URI prefixes and unconsumed original suffixes.
No production semantics or independent syntax is changed. -/
@[expose] public section
namespace MathGraph.WholeSource.DirectiveRecordBridge
open L4YAML L4YAML.Surface L4YAML.Scanner L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SourceEvents
open L4YAML.Proofs.CouplingBridge
open MathGraph.WholeSource.DirectiveBridge
open MathGraph.WholeSource.DirectiveRecords

def handleText (c : Char) : Bool :=
  !(c == ' ' || c == '\t' || c == '\r' || c == '\n')

lemma white_cases {c : Char} (h : isWhiteSpaceProp c) : c = ' ' ∨ c = '\t' := by
  simpa only [isWhiteSpaceProp, isSpaceProp, isTabProp, beq_iff_eq] using h

lemma handleText_true {c : Char} (h : isWordCharProp c ∨ c = '!') :
    handleText c = true := by
  by_cases hs : c = ' '
  · subst c; simp [isWordCharProp, isAsciiLetterProp] at h
  by_cases ht : c = '\t'
  · subst c; simp [isWordCharProp, isAsciiLetterProp] at h
  by_cases hr : c = '\r'
  · subst c; simp [isWordCharProp, isAsciiLetterProp] at h
  by_cases hn : c = '\n'
  · subst c; simp [isWordCharProp, isAsciiLetterProp] at h
  simp [handleText, hs, ht, hr, hn]

lemma drop_whites (ws rest : List Char) (h : ∀ c ∈ ws, isWhiteSpaceProp c) :
    dropHSpace (ws ++ rest) = dropHSpace rest := by
  induction ws with
  | nil => rfl
  | cons c cs ih =>
    have hc := white_cases (h c (by simp))
    have ht : ∀ d ∈ cs, isWhiteSpaceProp d := fun d hd => h d (by simp [hd])
    rcases hc with rfl | rfl <;> simpa [dropHSpace] using ih ht

lemma take_handle (cs rest : List Char)
    (h : ∀ c ∈ cs, isWordCharProp c ∨ c = '!') :
    (cs ++ rest).takeWhile handleText = cs ++ rest.takeWhile handleText := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := handleText_true (h c (by simp))
    have ht : ∀ d ∈ cs, isWordCharProp d ∨ d = '!' := fun d hd => h d (by simp [hd])
    simp [List.takeWhile, hc, ih ht]

lemma extract_spelling (ws handle sep rest : List Char)
    (hw : ∀ c ∈ ws, isWhiteSpaceProp c) (hwn : ws ≠ [])
    (hh : TagHandle handle)
    (hs : ∀ c ∈ sep, isWhiteSpaceProp c) (hsn : sep ≠ []) :
    explicitTagHandle ('%' :: 'T' :: 'A' :: 'G' :: (ws ++ handle ++ sep ++ rest)) =
      some handle := by
  cases ws with
  | nil => exact False.elim (hwn rfl)
  | cons c cs =>
    have hc := white_cases (hw c (by simp))
    have ht : ∀ d ∈ cs, isWhiteSpaceProp d := fun d hd => hw d (by simp [hd])
    have hd : dropHSpace (handle ++ sep ++ rest) = handle ++ sep ++ rest := by
      cases hh <;> rfl
    have hend : (sep ++ rest).takeWhile handleText = [] := by
      cases sep with
      | nil => exact False.elim (hsn rfl)
      | cons d ds =>
        rcases white_cases (hs d (by simp)) with rfl | rfl <;>
          simp [List.takeWhile, handleText]
    have htake : (handle ++ sep ++ rest).takeWhile handleText = handle := by
      rw [List.append_assoc, take_handle handle (sep ++ rest) hh.chars, hend]
      simp
    have hread : (dropHSpace (cs ++ handle ++ sep ++ rest)).takeWhile handleText = handle := by
      rw [show cs ++ handle ++ sep ++ rest = cs ++ (handle ++ sep ++ rest) by
        simp only [List.append_assoc]]
      rw [drop_whites cs _ ht, hd, htake]
    rcases hc with rfl | rfl <;>
      simp only [List.cons_append, explicitTagHandle, Bool.true_or, Bool.or_true,
        beq_self_eq_true, ite_true]
    all_goals
      change some ((dropHSpace (cs ++ handle ++ sep ++ rest)).takeWhile handleText) = some handle
      exact congrArg some hread

lemma percent_source {s t : SurfPos} (h : GLit '%' s t) :
    s.chars = '%' :: t.chars := by
  cases h
  rfl

/-- The raw source extractor agrees with EVERY independent TagDirective, not
just canonical spaces/LF or concrete handles. The original suffix is retained. -/
lemma extract_of_tagDirective {handle pfx : List Char} {s t : SurfPos}
    (h : TagDirective handle pfx s t) : explicitTagHandle s.chars = some handle := by
  have hp : s.chars = '%' :: h.afterPercent.chars := percent_source h.percent
  rw [hp, h.name.source, h.separatorRun.source, h.body.handleRun.source,
    h.body.separatorRun.source]
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using
    extract_spelling h.separator handle h.body.separator h.body.afterSeparator.chars
      h.separatorRun.chars h.separatorNonempty h.body.handleShape
      h.body.separatorRun.chars h.body.separatorNonempty

/-- The retained handle and actual scanner token agree at the same original
source span. Scanner correspondence and directive permission are explicit
local entry premises; this does not discharge the whole-source producer. -/
lemma scanner_record_agreement (sc : ScannerState) {handle pfx : List Char}
    {s t : SurfPos} (h : TagDirective handle pfx s t)
    (hc : ScannerSurfCorr sc s) (ha : sc.allowDirectives = true) :
    ∃ out, scanDirective sc = .ok out ∧ ScannerSurfCorr out t ∧
      explicitTagHandle s.chars = some handle ∧
      out.tokens = sc.tokens.push { pos := sc.currentPos, val := .tagDirective (String.ofList handle) (String.ofList pfx) } := by
  obtain ⟨out, hok, hc', ht, _⟩ := scanDirective_accepts sc h hc ha
  exact ⟨out, hok, hc', extract_of_tagDirective h, ht⟩

/-- At the actual initial scanner state, independent original-source syntax
supplies the correspondence and permission: neither is assumed by the caller.
This consumes one directive through its body, not the complete document. -/
lemma original_input_record_agreement (input : String) {handle pfx : List Char}
    {t : SurfPos} (h : TagDirective handle pfx ⟨input.toList, 0⟩ t) :
    ∃ out, scanDirective (ScannerState.mk' input) = .ok out ∧
      ScannerSurfCorr out t ∧ explicitTagHandle input.toList = some handle ∧
      out.tokens = (ScannerState.mk' input).tokens.push
        {pos := (ScannerState.mk' input).currentPos,
         val := .tagDirective (String.ofList handle) (String.ofList pfx)} :=
  scanner_record_agreement (ScannerState.mk' input) h
    (initial_corr input input.toList (chars_from_zero_toList input)) rfl

/-- Actual production dispatcher entry, not an instrumented directive runner.
The independent source judgment supplies the original initial state premises.
Only one scanNextToken call is closed; stream completion remains separate. -/
lemma original_dispatch_record_agreement (input : String) {handle pfx : List Char}
    {t : SurfPos} (h : TagDirective handle pfx ⟨input.toList, 0⟩ t) :
    let initial := (ScannerState.mk' input).emit .streamStart
    let ready := saveSimpleKey { initial with needIndentCheck := false }
    ∃ out, scanNextToken initial = .ok (some out) ∧ ScannerSurfCorr out t ∧
      explicitTagHandle input.toList = some handle ∧
      out.tokens = ready.tokens.push { pos := ready.currentPos, val := .tagDirective (String.ofList handle) (String.ofList pfx) } := by
  let initial := (ScannerState.mk' input).emit .streamStart
  let ready := saveSimpleKey { initial with needIndentCheck := false }
  have hp : input.toList = '%' :: h.afterPercent.chars := percent_source h.percent
  obtain ⟨hpre, hc, hf, _, ha, _⟩ :=
    MathGraph.WholeSource.DirectiveEntry.initial_percent_preprocess input _ hp
  have hcTag : ScannerSurfCorr ready ⟨input.toList, 0⟩ := by rw [hp]; exact hc
  obtain ⟨out, hdir, hout, he, ht⟩ := scanner_record_agreement ready h hcTag ha
  have hstruct := MathGraph.WholeSource.DirectiveEntry.percent_structural ready out _ hc hf hdir
  obtain ⟨hc1, hc2⟩ := MathGraph.WholeSource.DirectiveEntry.initial_checks input ready
  refine ⟨out, ?_, hout, he, ht⟩
  unfold scanNextToken
  rw [hpre]
  simp only [bind, Except.bind, pure, Except.pure]
  change (do
    scanNextToken_checkDanglingNode initial ready
    scanNextToken_checkFlowValueIndent initial ready
    match ← scanNextToken_dispatchStructural ready '%' with
    | some s => pure (some s)
    | none => _) = .ok (some out)
  rw [hc1]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [hc2]
  simp only []
  rw [hstruct]

#check original_dispatch_record_agreement
#check original_input_record_agreement
#check extract_of_tagDirective
#check scanner_record_agreement
open Lean Elab Command in
run_cmd do
  for n in [``extract_spelling, ``extract_of_tagDirective, ``scanner_record_agreement, ``original_input_record_agreement, ``original_dispatch_record_agreement] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"DIRECTIVE_RECORD_BRIDGE_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.DirectiveRecordBridge
