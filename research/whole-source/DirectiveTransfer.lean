module

public import DirectiveBridge
public meta import L4YAML.Scanner.Document

/-!
# Version-digit source bridges

Capstone path: independent version spelling → actual directive scanners →
Group 7.7 grammar completeness. The retained TAG collector proof is unchanged.
These lemmas stop at digit collection, not full YAML version acceptance.
-/
namespace MathGraph.WholeSource.DirectiveTransfer
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.StructureProduction
open MathGraph.WholeSource.DirectiveBridge

-- Boundary controls precede the general proofs. The major loop consumes '.',
-- while the minor loop must leave it at the next position.
#guard (collectVersionMinorLoop (ScannerState.mk' "12.x") "" 0).1 = ""
#guard (collectVersionMinorLoop (ScannerState.mk' "12.x") "" 1).1 = "1"
#guard (collectVersionMinorLoop (ScannerState.mk' "12.x") "" 2).1 = "12"
#guard (collectVersionMajorLoop (ScannerState.mk' "12.x") "" 2).2.peek? = some '.'
#guard (collectVersionMajorLoop (ScannerState.mk' "12.x") "" 3).2.peek? = some 'x'
#guard (collectVersionMajorLoop (ScannerState.mk' ".x") "" 1).2.peek? = some 'x'
#guard (collectVersionMinorLoop (ScannerState.mk' ".x") "" 1).2.peek? = some '.'
#guard (collectVersionMajorLoop (ScannerState.mk' "12.é") "old" 3).1 = "old12"

lemma digit_iff (c : Char) : c.isDigit = true ↔ isNsDecDigit c :=
  ⟨isNsDecDigit_of_isDigit, fun h => by
    by_cases hd : c.isDigit = true
    · exact hd
    · exact False.elim (not_isNsDecDigit_of_not_isDigit hd h)⟩

lemma digit_not_break (c : Char) (h : isNsDecDigit c) : c ≠ '\n' ∧ c ≠ '\r' := by
  constructor <;> intro he <;> subst c <;> simp [isNsDecDigit] at h

lemma minor_eq_collectRun (sc : ScannerState) (acc : String) (fuel : Nat) :
    collectVersionMinorLoop sc acc fuel = collectRun Char.isDigit sc acc fuel := by
  induction fuel generalizing sc acc with
  | zero => rfl
  | succ n ih =>
    cases hp : sc.peek? with
    | none => simp only [collectVersionMinorLoop, collectRun, hp]
    | some c =>
      simp only [collectVersionMinorLoop, collectRun, hp]
      split <;> simp_all only

/-- Direct transfer of the retained collector theorem to minor-version digits. -/
lemma minor_accepts (cs rest : List Char) (hcs : ∀ c ∈ cs, isNsDecDigit c)
    (hstop : Stops isNsDecDigit rest) (sc : ScannerState) (acc : String) (col fuel : Nat)
    (hcorr : ScannerSurfCorr sc ⟨cs ++ rest, col⟩) (hfuel : cs.length ≤ fuel) :
    ∃ out sc', collectVersionMinorLoop sc acc fuel = (out, sc') ∧
      out.toList = acc.toList ++ cs ∧
      ScannerSurfCorr sc' ⟨rest, col + cs.length⟩ ∧ Keeps sc sc' := by
  rw [minor_eq_collectRun]
  exact collectRun_accepts _ _ digit_iff digit_not_break cs hcs rest hstop sc acc col fuel hcorr hfuel

/-- Terminal-consumption adapter: the major collector has the same spelling as
minor collection but advances across its dot. Strictly more fuel is required. -/
lemma major_eq_minor_advance (cs rest : List Char) (hcs : ∀ c ∈ cs, isNsDecDigit c) :
    ∀ (sc : ScannerState) (acc : String) (col fuel : Nat),
      ScannerSurfCorr sc ⟨cs ++ '.' :: rest, col⟩ → cs.length < fuel →
      collectVersionMajorLoop sc acc fuel =
        let r := collectVersionMinorLoop sc acc fuel; (r.1, r.2.advance) := by
  induction cs with
  | nil =>
    intro sc acc col fuel hc hf
    cases fuel with
    | zero => simp at hf
    | succ n =>
      have hp := (peek_of_corr hc).1
      simp [collectVersionMajorLoop, collectVersionMinorLoop, hp, Char.isDigit]
  | cons c cs ih =>
    intro sc acc col fuel hc hf
    have hd := hcs c (by simp)
    have hne : c ≠ '.' := by intro he; subst c; simp [isNsDecDigit] at hd
    have hpk := (peek_of_corr hc).1
    have ha := advance_corr hc (digit_not_break c hd).1 (digit_not_break c hd).2
    cases fuel with
    | zero => simp at hf
    | succ n =>
      have step := ih (fun d hh => hcs d (by simp [hh])) sc.advance (acc.push c) (col+1) n ha (by simp at hf; omega)
      simpa [collectVersionMajorLoop, collectVersionMinorLoop, hpk, hne, (digit_iff c).mpr hd] using step

/-- Independent digit source followed by '.' determines the actual spelling
and landing after the dot, including arbitrary untouched UTF-8 suffixes. -/
lemma major_accepts (cs rest : List Char) (hcs : ∀ c ∈ cs, isNsDecDigit c)
    (sc : ScannerState) (acc : String) (col fuel : Nat)
    (hcorr : ScannerSurfCorr sc ⟨cs ++ '.' :: rest, col⟩) (hfuel : cs.length < fuel) :
    ∃ out sc', collectVersionMajorLoop sc acc fuel = (out, sc') ∧
      out.toList = acc.toList ++ cs ∧
      ScannerSurfCorr sc' ⟨rest, col + cs.length + 1⟩ ∧ Keeps sc sc' := by
  have hs : Stops isNsDecDigit ('.' :: rest) := by
    intro c hc
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst c
    simp [isNsDecDigit]
  obtain ⟨out, sc', heq, hout, hc', hk⟩ :=
    minor_accepts cs ('.' :: rest) hcs hs sc acc col fuel hcorr (by omega)
  refine ⟨out, sc'.advance, ?_, hout, ?_, hk.trans (keeps_advance sc')⟩
  · rw [major_eq_minor_advance cs rest hcs sc acc col fuel hcorr hfuel, heq]
  · exact advance_corr hc' (by decide) (by decide)

/-- Compose the adapted major collector with the reused minor collector on
one original source span. This is the version scanner's exact two-stage body,
using its real byte-derived fuel budgets. Numeric interpretation is separate. -/
lemma version_digits_accepts (major minor rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hstop : Stops isNsDecDigit rest) (sc : ScannerState) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨major ++ '.' :: (minor ++ rest), col⟩) :
    ∃ ma middle mi last,
      collectVersionMajorLoop sc "" (sc.inputEnd - sc.offset) = (ma, middle) ∧
      collectVersionMinorLoop middle "" (sc.inputEnd - middle.offset) = (mi, last) ∧
      ma.toList = major ∧ mi.toList = minor ∧
      ScannerSurfCorr last ⟨rest, col + major.length + 1 + minor.length⟩ ∧
      Keeps sc last := by
  have hf := fuel_of_corr hcorr
  obtain ⟨ma, middle, heq, hma', hmid, hk⟩ :=
    major_accepts major (minor ++ rest) hma sc "" col (sc.inputEnd - sc.offset) hcorr
      (by simp only [List.length_append, List.length_cons] at hf; omega)
  have hfmid := fuel_of_corr hmid
  obtain ⟨mi, last, heqmi, hmi', hend, hkeep⟩ :=
    minor_accepts minor rest hmi hstop middle "" (col + major.length + 1)
      (sc.inputEnd - middle.offset) hmid
      (by rw [hk.2.1] at hfmid; simp only [List.length_append] at hfmid; omega)
  exact ⟨ma, middle, mi, last, heq, heqmi, by simpa using hma',
    by simpa using hmi', hend, hk.trans hkeep⟩

-- Direct body controls also retain empty-digit and duplicate rejection.
private def bodyAccepts (input : String) (seen : Bool := false) : Bool :=
  let sc := { ScannerState.mk' input with seenYamlDirective := seen }
  (scanYamlDirective sc sc sc.currentPos).toOption.isSome
#guard bodyAccepts "1.2\n" = true
#guard bodyAccepts "001.002\né" = true
#guard bodyAccepts ".2\n" = false
#guard bodyAccepts "1.\n" = false
#guard bodyAccepts "1.2x\n" = false
#guard bodyAccepts "1.2\n" true = false

/-- Source-connected nonempty version digits ending before LF derive actual
YAML directive-body success. The incoming duplicate-version flag is explicit;
this does not establish a whole-stream version uniqueness invariant. -/
lemma yaml_body_before_lf (origin sc : ScannerState) (major minor rest : List Char)
    (hma : ∀ c ∈ major, isNsDecDigit c) (hmi : ∀ c ∈ minor, isNsDecDigit c)
    (hneMa : major ≠ []) (hneMi : minor ≠ []) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨major ++ '.' :: (minor ++ '\n' :: rest), col⟩)
    (hlimit : origin.inputEnd = sc.inputEnd) (hseen : origin.seenYamlDirective = false) :
    ∃ out, scanYamlDirective origin sc origin.currentPos = .ok out ∧
      ScannerSurfCorr out ⟨'\n' :: rest, col + major.length + 1 + minor.length⟩ ∧
      out.tokens = sc.tokens.push { pos := origin.currentPos, val := .versionDirective (String.ofList major).toNat! (String.ofList minor).toNat! } ∧
      out.seenYamlDirective = true ∧ out.directivesPresent = true := by
  have hs : Stops isNsDecDigit ('\n' :: rest) := by
    intro c hc
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst c
    simp [isNsDecDigit]
  obtain ⟨ma, middle, mi, last, heqMa, heqMi, hma', hmi', hlast, hk⟩ :=
    version_digits_accepts major minor ('\n' :: rest) hma hmi hs sc col hcorr
  have hmaEq : ma = String.ofList major := by
    rw [← String.toList_inj, String.toList_ofList]; exact hma'
  have hmiEq : mi = String.ofList minor := by
    rw [← String.toList_inj, String.toList_ofList]; exact hmi'
  subst ma; subst mi
  have hnonempty (cs : List Char) (hne : cs ≠ []) : (String.ofList cs).isEmpty = false := by
    apply String.isEmpty_eq_false_iff.mpr
    intro he
    have hh := congrArg String.toList he
    simp only [String.toList_ofList, String.toList_empty] at hh
    exact hne hh
  have hp := (peek_of_corr hlast).1
  have hws : skipWhitespace last = last :=
    L4YAML.Proofs.ScannerCoupling.skipWhitespace_noop last (by rw [hp]; decide)
  let final := { last.emitAt origin.currentPos
      (.versionDirective (String.ofList major).toNat! (String.ofList minor).toNat!) with
        seenYamlDirective := true, directivesPresent := true }
  have hfinal : ScannerSurfCorr final ⟨'\n' :: rest, col + major.length + 1 + minor.length⟩ := by
    have he := L4YAML.Proofs.ScalarCoupling.corr_of_emitAt origin.currentPos
      (.versionDirective (String.ofList major).toNat! (String.ofList minor).toNat!) hlast
    exact ⟨he.chars_from, he.col_eq, he.end_eq, he.input_prefix, he.indent_cols_nonneg⟩
  refine ⟨final, ?_, hfinal, ?_, rfl, rfl⟩
  · unfold scanYamlDirective
    simp [hseen, hlimit, heqMa, heqMi, hws, hp, hnonempty major hneMa,
      hnonempty minor hneMi, L4YAML.CharPredicates.isLineBreakBool,
      L4YAML.CharPredicates.isLineFeedBool, L4YAML.CharPredicates.isCarriageReturnBool, final]
  · simp only [final, ScannerState.emitAt]
    rw [hk.1]

#print axioms minor_accepts
#print axioms major_eq_minor_advance
#print axioms major_accepts
#print axioms version_digits_accepts
#print axioms yaml_body_before_lf
end
end MathGraph.WholeSource.DirectiveTransfer
