/-
Seven-byte source-indexed annotated grammar discriminator, 2026-11-21.

Source baseline: e389fcb62b95b9da954bd81c14427d56e3417dfd.
Goal NOT ASSUMED: either construct a true TLYamlStream/TraceOf derivation
for "? -\\n  :" up to the real document marker or prove its non-membership.
This file checks the smallest factual indentation boundary first, using
the *actual* L4YAML.Surface.SIndent/GLit relations. These local lemmas
alone do NOT imply global TLYamlStream non-membership or refute S3.
-/
module
public import L4YAML.Proofs.Serialization.TraceOf.Reachability
public import L4YAML.Parser.TokenParser
public meta import L4YAML.Proofs.Serialization.TraceOf.Reachability
public meta import L4YAML.Parser.TokenParser
@[expose] public section Blanket

namespace L4YAML.Tests.Guards.AnnotatedColonDecision
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.TraceOf

/-- This source position is at the beginning of the colon line in
    the exact seven-byte body. -/
def twoSpacesBeforeColon (rest : List Char) : SurfPos :=
  ⟨' ' :: ' ' :: ':' :: rest, 0⟩
def nestedColon (rest : List Char) : SurfPos := ⟨':' :: rest, 2⟩

/-- The actual [63] SIndent 0 cannot make the two spaces disappear. -/
theorem no_root_indent_to_nested_colon (rest : List Char) :
    ¬ SIndent 0 (twoSpacesBeforeColon rest) (nestedColon rest) := by
  intro h
  cases h

/-- Stronger: a root explicit mapping's [186] zero-indent colon arm
    cannot consume a ':' after two leading spaces, whatever endpoint
    the consumer proposes. -/
theorem no_root_colon (rest : List Char) :
    ¬ ∃ (mid stop : SurfPos),
      SIndent 0 (twoSpacesBeforeColon rest) mid ∧ GLit ':' mid stop := by
  rintro ⟨mid, stop, hi, hc⟩
  cases hi
  cases hc

/-- Positive control: this source DOES admit two indentation spaces. -/
theorem nested_indent_two (rest : List Char) :
    SIndent 2 (twoSpacesBeforeColon rest) (nestedColon rest) := by
  unfold twoSpacesBeforeColon nestedColon
  exact SIndent.succ 1 (' ' :: ':' :: rest) 0 _
    (SIndent.succ 0 (':' :: rest) 1 _ (.zero _))

/-- Positive control: after genuine two-space indentation, ':' matches. -/
theorem nested_colon_literal (rest : List Char) :
    GLit ':' (nestedColon rest) ⟨rest, 3⟩ := by
  exact .mk rest 2

/- The *same* native scanner/parser split, not a substituted model. -/
#guard (scanFiltered "? -\n  :").isOk
#guard !((scanFiltered "? -\n  :").bind
  (fun ts => L4YAML.TokenParser.parseStream ts)).isOk

/-- Explicitly record what remains unproved; naming a Prop is no evidence. -/
def FullStreamNonmembershipGoal : Prop :=
  ∀ ev, ¬ TraceOf "? -\n  :\n...\n%YAML 1.2\n---\ny" ev

#print axioms L4YAML.Tests.Guards.AnnotatedColonDecision.no_root_colon
#print axioms L4YAML.Tests.Guards.AnnotatedColonDecision.nested_indent_two
#print axioms L4YAML.Tests.Guards.AnnotatedColonDecision.nested_colon_literal

end L4YAML.Tests.Guards.AnnotatedColonDecision
end Blanket
