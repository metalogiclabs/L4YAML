module
public import DirectiveRecords
public import DirectiveBridge
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
    rcases hc with rfl | rfl <;>
      simp only [List.cons_append, explicitTagHandle, Bool.true_or, Bool.false_or,
        beq_self_eq_true, reduceBEq, ite_true]
    all_goals
      change some ((dropHSpace (cs ++ (handle ++ sep ++ rest))).takeWhile handleText) = some handle
      rw [drop_whites cs _ ht, hd, htake]

/-- The raw source extractor agrees with EVERY independent TagDirective, not
just canonical spaces/LF or concrete handles. The original suffix is retained. -/
lemma extract_of_tagDirective {handle prefix : List Char} {s t : SurfPos}
    (h : TagDirective handle prefix s t) : explicitTagHandle s.chars = some handle := by
  have hp : s.chars = '%' :: h.afterPercent.chars := by cases h.percent; rfl
  rw [hp, h.name.source, h.separatorRun.source, h.body.handleRun.source,
    h.body.separatorRun.source]
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using
    extract_spelling h.separator handle h.body.separator h.body.afterSeparator.chars
      h.separatorRun.chars h.separatorNonempty h.body.handleShape
      h.body.separatorRun.chars h.body.separatorNonempty

/-- The retained handle and actual scanner token agree at the same original
source span. Scanner correspondence and directive permission are explicit
local entry premises; this does not discharge the whole-source producer. -/
lemma scanner_record_agreement (sc : ScannerState) {handle prefix : List Char}
    {s t : SurfPos} (h : TagDirective handle prefix s t)
    (hc : ScannerSurfCorr sc s) (ha : sc.allowDirectives = true) :
    ∃ out, scanDirective sc = .ok out ∧ ScannerSurfCorr out t ∧
      explicitTagHandle s.chars = some handle ∧
      out.tokens = sc.tokens.push {pos := sc.currentPos,
        val := .tagDirective (String.ofList handle) (String.ofList prefix)} := by
  obtain ⟨out, hok, hc', ht, _⟩ := scanDirective_accepts sc h hc ha
  exact ⟨out, hok, hc', extract_of_tagDirective h, ht⟩

#check extract_of_tagDirective
#check scanner_record_agreement
open Lean Elab Command in
run_cmd do
  for n in [``extract_spelling, ``extract_of_tagDirective, ``scanner_record_agreement] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"DIRECTIVE_RECORD_BRIDGE_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.DirectiveRecordBridge
