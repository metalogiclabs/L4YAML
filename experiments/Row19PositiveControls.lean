module

public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Proofs.Serialization.TraceOf.Document

/-! # Independent decision-equivalence adequacy witness (source-derived) -/

namespace L4YAML.Tests.Guards.TraceOfBlockAmbiguity

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

/-! ## Refutation 1 (OPEN — row 19 `implicitContinue`): `a⏎*x` -/
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

lemma traceOf_plain : TraceOf "a\n*x" [] := ⟨2, readPlain⟩

end ImplicitContinue

lemma emptyEventsWellFormed : SerializationWellFormed ([] : List Event) := by
  apply (serializationWellFormed_iff_check _).mpr
  decide

#check traceOf_plain
#print axioms traceOf_plain
#check emptyEventsWellFormed

#eval if (L4YAML.TokenParser.parseYaml "a\n*x").isOk then
  "SCALAR_ACCEPT" else "SCALAR_REJECT"
#eval if (L4YAML.TokenParser.parseYaml "a\n---\nb").isOk then
  "EXPLICIT_CONTINUE_ACCEPT" else "EXPLICIT_CONTINUE_REJECT"
#eval if (L4YAML.TokenParser.parseYaml "a\n---\n*x").isOk then
  "UNDEFINED_ALIAS_ACCEPT" else "UNDEFINED_ALIAS_REJECT"

end L4YAML.Tests.Guards.TraceOfBlockAmbiguity
