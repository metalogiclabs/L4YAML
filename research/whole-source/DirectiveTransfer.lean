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

#print axioms minor_accepts
#print axioms major_eq_minor_advance
#print axioms major_accepts
end
end MathGraph.WholeSource.DirectiveTransfer
