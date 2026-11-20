/-
Capstone: Blueprint 7.7, external YAML 1.2.2 requirement coverage.

Constructive annotated-grammar witnesses for one versus two identical TAG
directives in a single explicit document. Both derivations use only the
single-document stream constructor and the actual directive grammar.
Neither scanner acceptance nor parser acceptance is a premise.

The second input violates YAML 1.2.2 section 6.8.2's one-TAG-directive-per-
handle restriction. This file proves what the present formal grammar admits;
it does not assert that this grammar faithfully formalizes that restriction.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.Document

@[expose] public section Blanket

namespace L4YAML.Tests.Guards.TagDirectiveAnnotated

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

set_option maxHeartbeats 1000000

def singleInput : String := "%TAG ! !x\n--- a"
def duplicateInput : String := "%TAG ! !x\n%TAG ! !x\n--- a"

-- Pin actual line feeds and keep the duplicate within one directive document.
#guard singleInput.toList = ['%', 'T', 'A', 'G', ' ', '!', ' ', '!', 'x', '\n', '-', '-', '-', ' ', 'a']
#guard duplicateInput.utf8ByteSize = 25

/-- One complete directive line, independently of what follows it. -/
lemma tag_line (tail : List Char) :
    SLDirective ⟨"%TAG ! !x\n".toList ++ tail, 0⟩ ⟨tail, 0⟩ := by
  refine SLDirective.tag
    ([' ', '!', ' ', '!', 'x', '\n'] ++ tail) 0
    ⟨['!', ' ', '!', 'x', '\n'] ++ tail, 5⟩
    ⟨[' ', '!', 'x', '\n'] ++ tail, 6⟩
    ⟨['!', 'x', '\n'] ++ tail, 7⟩
    ⟨'\n' :: tail, 9⟩ ⟨tail, 0⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t h
    cases h with
    | mk _ _ _ hp =>
      have hn : ¬ isNsChar ' ' := by unfold isNsChar; decide
      exact hn hp
  · exact .cons _ _ _ (.space _ _) (.nil _)
  · exact .cons _ _ _ (.mk '!' _ _ (by decide)) (.nil _)
  · intro t h
    cases h with
    | mk _ _ _ hp =>
      have hn : ¬ (isWordCharProp ' ' ∨ ' ' = '!') := by decide
      exact hn hp
  · exact .cons _ _ _ (.space _ _) (.nil _)
  · exact .cons _ _ _ (.mk '!' _ _ (by decide))
      (.cons _ _ _ (.mk 'x' _ _ (by decide)) (.nil _))
  · exact .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf _ _))) (.nil _)

/-- The actual TLDirective annotation drops a primary-handle declaration. -/
lemma single_directive :
    TLDirective ⟨singleInput.toList, 0⟩ ⟨"--- a".toList, 0⟩ [] := by
  constructor
  · exact tag_line "--- a".toList
  · decide

lemma duplicate_first_directive :
    TLDirective ⟨duplicateInput.toList, 0⟩ ⟨singleInput.toList, 0⟩ [] := by
  constructor
  · exact tag_line singleInput.toList
  · decide

/-- The explicit document's body is the plain scalar a, with no events. -/
lemma explicit_body :
    TLExplicitBody ⟨[' ', 'a'], 3⟩ ⟨[], 5⟩ [] := by
  apply TAlt.left
  apply TLBareDocument.mk
  refine TBlockNode.flowInBlock 0 .blockIn _ ⟨['a'], 4⟩ ⟨[], 5⟩ _ [] ?_ ?_ ?_
  · exact SSeparateLines.inline _ _ _
      (.whites _ _ (.mk _ _ _ (.space _ _) (.nil _)))
  · apply TFlowNode.content
    apply TFlowContent.plain
    exact SNsPlainMultiLine.mk _ _ _ _ _
      (.mk _ _ _ _ (.nonIndicator _ 'a' [] 4
        (by unfold isNsPlainSafe isNsChar; decide) (by decide)) (.nil _))
      (.nil _)
  · exact SSLComments.withComment _ _ _ (.noSep _ _ (.eof 5)) (.nil _)

/-- A valid single declaration has precisely this constructed trace. -/
lemma single_trace : TraceOf singleInput [.beginDocument] := by
  refine ⟨5, TLYamlStream.single _ _ _ _ [.beginDocument] [] (.nil _) ?_ (.nil _)⟩
  apply TOpt.some
  apply TLAnyDocument.directive
  exact TLDirectiveDocument.mk _ ⟨"--- a".toList, 0⟩ ⟨[' ', 'a'], 3⟩ _ [] []
    (TPlus.mk _ _ _ [] [] single_directive (.nil _))
    (SCDirectivesEnd.mk _) explicit_body

/-- The duplicate declaration also has that trace, without an implicit stream
continuation or scannerDrop. Tightening implicitContinue cannot remove this
single-document derivation. -/
lemma duplicate_trace : TraceOf duplicateInput [.beginDocument] := by
  refine ⟨5, TLYamlStream.single _ _ _ _ [.beginDocument] [] (.nil _) ?_ (.nil _)⟩
  apply TOpt.some
  apply TLAnyDocument.directive
  exact TLDirectiveDocument.mk _ ⟨"--- a".toList, 0⟩ ⟨[' ', 'a'], 3⟩ _ [] []
    (TPlus.mk _ _ _ [] [] duplicate_first_directive
      (TStar.cons _ _ _ [] [] single_directive (.nil _)))
    (SCDirectivesEnd.mk _) explicit_body

lemma common_trace_well_formed : SerializationWellFormed [.beginDocument] := by
  trivial

end L4YAML.Tests.Guards.TagDirectiveAnnotated

#print axioms L4YAML.Tests.Guards.TagDirectiveAnnotated.single_trace
#print axioms L4YAML.Tests.Guards.TagDirectiveAnnotated.duplicate_trace
#print axioms L4YAML.Tests.Guards.TagDirectiveAnnotated.common_trace_well_formed

end Blanket
