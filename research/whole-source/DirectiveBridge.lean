module

public import L4YAML.Proofs.Production.Acceptance.Properties

/-!
# Independent TAG lexical grammar and scanner bridge

Research dependency path: independent directive syntax → scanner acceptance →
`parse_iff_grammar` (the open grammar-completeness capstone). This module changes
no production grammar or runtime. Qualification requires exact-source CI and
axiom inspection; source text alone makes no passing claim.
-/

namespace MathGraph.WholeSource.DirectiveBridge

@[expose] public section

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.Acceptance
open L4YAML.Proofs.StructureProduction

/-- Independent [89]–[92] spelling: named handles have a nonempty word body. -/
inductive TagHandle : List Char → Prop where
  | primary : TagHandle ['!']
  | secondary : TagHandle ['!', '!']
  | named (c : Char) (cs : List Char) (hc : isWordCharProp c)
      (hcs : ∀ d ∈ cs, isWordCharProp d) : TagHandle ('!' :: (c :: cs) ++ ['!'])

/-- Scanner-independent maximal-run boundary. -/
def Stops (p : Char → Prop) (rest : List Char) : Prop :=
  ∀ c, rest.head? = some c → ¬ p c

/-- An instrument used only to share the three collector proofs. -/
def collectRun (test : Char → Bool) (sc : ScannerState) (acc : String) :
    Nat → String × ScannerState
  | 0 => (acc, sc)
  | n + 1 => match sc.peek? with
    | none => (acc, sc)
    | some c => if test c then collectRun test sc.advance (acc.push c) n else (acc, sc)

/-- A maximal independent character run determines the exact returned spelling
and original-input landing, for every scanner state corresponding to its start. -/
lemma collectRun_accepts (p : Char → Prop) (test : Char → Bool)
    (htest : ∀ c, test c = true ↔ p c)
    (hbreak : ∀ c, p c → c ≠ '\n' ∧ c ≠ '\r')
    (cs : List Char) (hcs : ∀ c ∈ cs, p c)
    (rest : List Char) (hstop : Stops p rest) :
    ∀ (sc : ScannerState) (acc : String) (col fuel : Nat),
      ScannerSurfCorr sc ⟨cs ++ rest, col⟩ → cs.length ≤ fuel →
      ∃ out sc', collectRun test sc acc fuel = (out, sc') ∧
        out.toList = acc.toList ++ cs ∧
        ScannerSurfCorr sc' ⟨rest, col + cs.length⟩ ∧ Keeps sc sc' := by
  induction cs with
  | nil =>
    intro sc acc col fuel hcorr _
    refine ⟨acc, sc, ?_, by simp, by simpa using hcorr, Keeps.refl sc⟩
    cases fuel with
    | zero => rfl
    | succ n =>
      cases rest with
      | nil => simp [collectRun, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        have hc : test c = false := by
          cases hb : test c
          · rfl
          · exact False.elim ((hstop c rfl) ((htest c).mp hb))
        simp [collectRun, hpk, hc]
  | cons c cs ih =>
    intro sc acc col fuel hcorr hfuel
    have hc := hcs c (by simp)
    have ht : ∀ d ∈ cs, p d := fun d hd => hcs d (by simp [hd])
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hpk := (peek_of_corr hcorr).1
      have hadv := advance_corr hcorr (hbreak c hc).1 (hbreak c hc).2
      obtain ⟨out, sc', heq, hout, hcorr', hk⟩ :=
        ih ht sc.advance (acc.push c) (col + 1) n hadv (by simp at hfuel; omega)
      refine ⟨out, sc', ?_, ?_, ?_, (keeps_advance sc).trans hk⟩
      · simp [collectRun, hpk, (htest c).mpr hc, heq]
      · simpa [String.toList_push, List.append_assoc] using hout
      · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcorr'

lemma handleLoop_eq_collectRun (sc : ScannerState) (acc : String) (fuel : Nat) :
    collectTagHandleDirectiveLoop sc acc fuel =
      collectRun (fun c => isWordCharBool c || c == '!') sc acc fuel := by
  induction fuel generalizing sc acc with
  | zero => rfl
  | succ n ih =>
    simp only [collectTagHandleDirectiveLoop, collectRun]
    split
    · split
      · exact ih _ _
      · rfl
    · rfl

lemma handleChar_not_break (c : Char) (h : isWordCharProp c ∨ c = '!') :
    c ≠ '\n' ∧ c ≠ '\r' := by
  rcases h with hw | rfl
  · exact wordChar_not_break hw
  · decide

lemma TagHandle.chars {cs : List Char} (h : TagHandle cs) :
    ∀ c ∈ cs, isWordCharProp c ∨ c = '!' := by
  cases h with
  | primary => simp
  | secondary => simp
  | named c cs hc hcs =>
    intro d hd
    simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hd
    rcases hd with rfl | ((rfl | hd) | rfl)
    · exact Or.inr rfl
    · exact Or.inl hc
    · exact Or.inl (hcs d hd)
    · exact Or.inr rfl

/-- The runtime validator accepts every independently generated handle. -/
lemma TagHandle.validated {cs : List Char} (h : TagHandle cs) :
    isTagHandleShaped (String.ofList cs) = true := by
  cases h with
  | primary => decide
  | secondary => decide
  | named c cs hc hcs =>
    have hw : (c :: cs).all isWordCharBool = true := by
      simp only [List.all_eq_true]
      intro d hd
      apply (isWordChar_iff d).mpr
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hc
      · exact hcs d hd
    simp [isTagHandleShaped, String.toList_ofList, hw, List.length_append,
      List.getLast?_append]

/-- Stable public collector signature. It covers arbitrary primary, secondary,
and named handles, arbitrary UTF-8 suffixes, scanner context and accumulator. -/
lemma collectTagHandleDirectiveLoop_accepts {cs rest : List Char}
    (h : TagHandle cs) (hstop : Stops (fun c => isWordCharProp c ∨ c = '!') rest)
    (sc : ScannerState) (acc : String) (col fuel : Nat)
    (hcorr : ScannerSurfCorr sc ⟨cs ++ rest, col⟩) (hfuel : cs.length ≤ fuel) :
    ∃ out sc', collectTagHandleDirectiveLoop sc acc fuel = (out, sc') ∧
      out.toList = acc.toList ++ cs ∧
      ScannerSurfCorr sc' ⟨rest, col + cs.length⟩ ∧ Keeps sc sc' := by
  rw [handleLoop_eq_collectRun]
  exact collectRun_accepts _ _ isTagHandleChar_iff_bool handleChar_not_break
    cs h.chars rest hstop sc acc col fuel hcorr hfuel

lemma handle_empty_excluded : ¬ TagHandle [] := by intro h; cases h
lemma handle_unclosed_excluded : ¬ TagHandle ['!', 'a'] := by intro h; cases h

-- Constructive reachability of all three grammar arms.
lemma primary_witness : TagHandle ['!'] := .primary
lemma secondary_witness : TagHandle ['!', '!'] := .secondary
lemma named_witness : TagHandle ['!', 'a', '!'] :=
  .named 'a' [] (by decide) (by simp)

#print axioms collectTagHandleDirectiveLoop_accepts
#print axioms TagHandle.validated

end
end MathGraph.WholeSource.DirectiveBridge
