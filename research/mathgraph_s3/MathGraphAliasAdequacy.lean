module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Serialization.TraceOf.Document

/-! # `traceOf_unique` on the block/document fragment (Rule 2): refutations -/

namespace L4YAML.Tests.Guards.MathGraphAliasAdequacy

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

private lemma ns_x : isNsAnchorChar 'x' := by unfold isNsAnchorChar isNsChar; decide
private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma nsc_star : isNsChar '*' := by unfold isNsChar; decide
private lemma nsc_x : isNsChar 'x' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

/-! ## Refutation 1 (OPEN — row 19 `implicitContinue`): `a⏎&x` -/
section ImplicitContinue

abbrev u0 : SurfPos := ⟨['a', '\n', '*', 'x'], 0⟩
abbrev u1 : SurfPos := ⟨['\n', '*', 'x'], 1⟩
abbrev u2 : SurfPos := ⟨['*', 'x'], 0⟩
abbrev u3 : SurfPos := ⟨['x'], 1⟩
abbrev u4 : SurfPos := ⟨[], 2⟩

/-- Reading A (the parser's): one bare document, plain scalar `a *x` folded over the break. -/
lemma readPlain : TLYamlStream u0 u4 [] :=
  .single u0 u0 u4 u4 [] [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _
      (.flowInBlock 0 .blockIn u0 u0 u4 u4 []
        (.inline 0 _ _ (.startOfLine _))
        (.content 0 .flowOut u0 u4 [] (.plain 0 .flowOut u0 u4
          (SNsPlainMultiLine.mk 0 .flowOut u0 u1 u4
            (SNsPlainOneLine.mk .flowOut u0 u1 u1
              (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
            (.cons u1 u4 u4
              (SSNsPlainNextLine.mk 0 .flowOut u1 u1 u2 u2 u2 u3 u4
                (.nil _) (SBBreak.lf _ 1) (.nil _)
                (SFlowLinePrefix.mk 0 u2 u2 u2 (.zero _) (.none _))
                (SNsPlainChar.safe .flowOut '*' _ 0 nsc_star (by decide) (by decide))
                (.cons u3 u4 u4
                  (SNbNsPlainInLineEntry.mk .flowOut u3 u3 u4 (.nil _)
                    (SNsPlainChar.safe .flowOut 'x' _ 1 nsc_x (by decide) (by decide)))
                  (.nil _)))
              (.nil _)))))
        (eofComments 2)))))
    (.nil _)

/-- Reading B: bare document `a`, then `implicitContinue` with a second BARE document `*x`. -/
lemma readAlias : TLYamlStream u0 u4 [Event.useAlias "x"] :=
  .implicitContinue u0 u2 u2 u4 u4 [] [Event.useAlias "x"] []
    (.single u0 u0 u2 u2 [] [] (.nil _)
      (.some _ _ _ (.bare _ _ _ (.mk _ _ _
        (.flowInBlock 0 .blockIn u0 u0 u1 u2 []
          (.inline 0 _ _ (.startOfLine _))
          (.content 0 .flowOut u0 u1 [] (.plain 0 .flowOut u0 u1
            (SNsPlainMultiLine.mk 0 .flowOut u0 u1 u1
              (SNsPlainOneLine.mk .flowOut u0 u1 u1
                (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
              (.nil _))))
          (.withComment u1 u2 u2 (.noSep _ _ (.break _ _ (SBBreak.lf _ 1))) (.nil _))))))
      (.nil _))
    (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _
      (.flowInBlock 0 .blockIn u2 u2 u4 u4 [Event.useAlias "x"]
        (.inline 0 _ _ (.startOfLine _))
        (.alias 0 .flowOut u2 u4 _
          (And.intro
            (SCNsAliasNode.mk _ 0 u4
              (GPlus.mk _ _ _ (GChar.mk 'x' _ 1 ns_x) (.nil _))
              (fun _ hg => by cases hg))
            (by decide)))
        (eofComments 2)))))
    (.nil _)

lemma traceOf_plain : TraceOf "a\n*x" [] := ⟨2, readPlain⟩
lemma traceOf_alias : TraceOf "a\n*x" [Event.useAlias "x"] := ⟨2, readAlias⟩

/-- `traceOf_unique` is FALSE as stated while `implicitContinue` admits a second bare document. -/
lemma traceOf_unique_refuted :
    ¬ (∀ (input : String) (ev₁ ev₂ : List Event),
        TraceOf input ev₁ → TraceOf input ev₂ → ev₁ = ev₂) :=
  fun h => by cases h _ _ _ traceOf_plain traceOf_alias

end ImplicitContinue
/-- A single alias use has no preceding declaration. -/
lemma orphanAliasRefused : ¬ SerializationWellFormed [Event.useAlias "x"] := by
  intro h
  have hCheck := (serializationWellFormed_iff_check [Event.useAlias "x"]).mp h
  have noCheck : checkFrom ({} : Env) [Event.useAlias "x"] = false := by decide
  rw [noCheck] at hCheck
  cases hCheck

/-- Current universal trace-well-formedness is false for this one input. -/
lemma traceWellFormed_refuted : ¬ TraceWellFormed "a\n*x" := by
  intro h
  exact orphanAliasRefused (h _ traceOf_alias)

#guard (L4YAML.TokenParser.parseYaml "a\n*x").isOk
#eval (L4YAML.TokenParser.parseYaml "a\n*x").isOk

end L4YAML.Tests.Guards.MathGraphAliasAdequacy
