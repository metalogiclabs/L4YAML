/- Exact original-upstream forward-contract counterexample.
Capstone: Blueprint 7.7, admission of its stated biconditional contract.
Library source identity: 14eb6dba / cbc2ca9d, L4YAML tree
4197c0b6f2fb369e9806ca486d38aef87b077c81.
No production source changes; no custom axioms or native_decide.
The refutation concerns the current fixed TraceWellFormed definition.
It says nothing about a future capstone with corrected grammar semantics. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Parser.Composition
-- The same import used by the repository's ParserNodeProofs exposes
-- Std.Legacy.Range.forIn' to kernel reduction across the module boundary.
import all Init.Data.Range.Basic
@[expose] public section Blanket

namespace L4YAML.Tests.Guards.UpstreamForwardCounterexample
open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

def input : String := "a\n*x"
#guard input.toList = ['a', '\n', '*', 'x']
#guard input.utf8ByteSize = 4

/-- Positive runtime control on the same original parser. -/
lemma empty_parser_control : (TokenParser.parseYaml "").isOk = true := by cbv

/-- Positive grammar control on the same original trace relation. -/
lemma empty_trace_control : TraceOf "" [] := traceOf_empty

abbrev u0 : SurfPos := ⟨['a', '\n', '*', 'x'], 0⟩
abbrev u1 : SurfPos := ⟨['\n', '*', 'x'], 1⟩
abbrev u2 : SurfPos := ⟨['*', 'x'], 0⟩
abbrev u3 : SurfPos := ⟨['x'], 1⟩
abbrev u4 : SurfPos := ⟨[], 2⟩

private lemma ns_x : isNsAnchorChar 'x' := by unfold isNsAnchorChar isNsChar; decide
private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

lemma first_bare : TLBareDocument u0 u2 [] :=
  .mk _ _ _
    (.flowInBlock 0 .blockIn u0 u0 u1 u2 []
      (.inline 0 _ _ (.startOfLine _))
      (.content 0 .flowOut u0 u1 [] (.plain 0 .flowOut u0 u1
        (SNsPlainMultiLine.mk 0 .flowOut u0 u1 u1
          (SNsPlainOneLine.mk .flowOut u0 u1 u1
            (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
          (.nil _))))
      (.withComment u1 u2 u2 (.noSep _ _ (.break _ _ (SBBreak.lf _ 1))) (.nil _)))

lemma second_bare : TLBareDocument u2 u4 [.useAlias "x"] :=
  .mk _ _ _
    (.flowInBlock 0 .blockIn u2 u2 u4 u4 [.useAlias "x"]
      (.inline 0 _ _ (.startOfLine _))
      (.alias 0 .flowOut u2 u4 [.useAlias "x"]
        (And.intro
          (SCNsAliasNode.mk _ 0 u4
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 1 ns_x) (.nil _))
            (fun _ hg => by cases hg))
          (by decide)))
      (.withComment _ _ _ (.noSep _ _ (.eof 2)) (.nil _)))

lemma bad_trace : TraceOf input [.useAlias "x"] := by
  have first : TLYamlStream u0 u2 [] :=
    .single _ _ _ _ [] [] (.nil _)
      (.some _ _ _ (.bare _ _ _ first_bare)) (.nil _)
  exact ⟨2, .implicitContinue _ _ _ _ _ [] [.useAlias "x"] [] first (.nil _)
    (.some _ _ _ (.bare _ _ _ second_bare)) (.nil _)⟩

lemma not_trace_well_formed : ¬ TraceWellFormed input := by
  intro h
  have hb := h [.useAlias "x"] bad_trace
  simp [SerializationWellFormed, WellFormedFrom, AliasAllowed] at hb

/-- Kernel reduction of the exact executable pipeline's success bit. -/
lemma parser_accepts_bit : (TokenParser.parseYaml input).isOk = true := by
  cbv

lemma parser_accepts : ∃ docs, TokenParser.parseYaml input = .ok docs := by
  have h := parser_accepts_bit
  cases hs : TokenParser.parseYaml input with
  | ok docs => exact ⟨docs, rfl⟩
  | error e =>
    rw [hs] at h
    change false = true at h
    cases h

lemma universal_forward_serialization_refuted :
    ¬ (∀ (s : String) (docs : Array YamlDocument),
      TokenParser.parseYaml s = .ok docs → TraceWellFormed s) := by
  intro h
  obtain ⟨docs, hp⟩ := parser_accepts
  exact not_trace_well_formed (h input docs hp)

/-- No choice of the still-unpaid exact-surface predicate can make the
documented biconditional true while this upstream TraceWellFormed is fixed.
The accepted four-byte input already falsifies its forward consequence. -/
lemma no_biconditional (ExactSurfaceLanguage : String → Prop) :
    ¬ (∀ s : String,
      (∃ docs, TokenParser.parseYaml s = .ok docs) ↔
        ExactSurfaceLanguage s ∧ TraceWellFormed s) := by
  intro h
  exact not_trace_well_formed ((h input).mp parser_accepts).2

#print axioms empty_parser_control
#print axioms empty_trace_control
#print axioms bad_trace
#print axioms not_trace_well_formed
#print axioms parser_accepts_bit
#print axioms parser_accepts
#print axioms universal_forward_serialization_refuted
#print axioms no_biconditional

end L4YAML.Tests.Guards.UpstreamForwardCounterexample
end Blanket
