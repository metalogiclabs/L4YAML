module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Parser.Composition

/-!
# Answer-relative source-trace audit

Source pin: nasa-jpl/L4YAML 64795a8db28ccfdae85082c93b6453001ae9d3e4.

This is an out-of-tree diagnostic, not a proposed library capstone. The upstream
guard TraceOfBlockAmbiguity already refutes full trace equality using `a\n&x`.
Here the cheapest stronger question is posed for testing: can trace equality be
replaced by agreement on serialization well-formedness? Replacing `&x` by `*x`
is expected to make the two readings disagree on the protected answer itself. The witnesses below
are adapted, with attribution, from that existing upstream guard; the new
proposed consequence is the failure of the universal `TraceWellFormed` predicate
on an input the actual parser is expected to accept.

STATUS: CANDIDATE proof terms awaiting compilation. Execution in this workspace
was blocked by Lean's required `/proc/<pid>/exe` lookup permission. No successful
native build, axiom inspection, or runtime evaluation is claimed.

The source-trace and semantic obligations use ordinary term proofs. Only the
executable acceptance control uses `native_decide`, separately named; axiom
inspection commands are supplied below but have not run. No scannerDrop
constructor is used anywhere here.
-/

namespace MathGraph.TraceAnswerAudit

@[expose] public section

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

private lemma ns_x : isNsAnchorChar 'x' := by
  unfold isNsAnchorChar isNsChar
  decide

private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma nsc_star : isNsChar '*' := by unfold isNsChar; decide
private lemma nsc_x : isNsChar 'x' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

abbrev u0 : SurfPos := ⟨['a', '\n', '*', 'x'], 0⟩
abbrev u1 : SurfPos := ⟨['\n', '*', 'x'], 1⟩
abbrev u2 : SurfPos := ⟨['*', 'x'], 0⟩
abbrev u3 : SurfPos := ⟨['x'], 1⟩
abbrev u4 : SurfPos := ⟨[], 2⟩

/-- Reading A: one bare document, the plain scalar `a *x`. -/
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

/-- Reading B: bare `a`, then an unmarked second bare document `*x`.
The permissive `[211]` arm, not a scanner operation, creates the second reading. -/
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
        (.alias 0 .flowOut u2 u4 [Event.useAlias "x"]
          ⟨SCNsAliasNode.mk _ 0 u4
            (GPlus.mk _ _ _ (GChar.mk 'x' _ 1 ns_x) (.nil _))
            (fun _ hg => by cases hg), by decide⟩)
        (eofComments 2)))))
    (.nil _)

lemma traceOf_plain : TraceOf "a\n*x" [] := ⟨2, readPlain⟩
lemma traceOf_alias : TraceOf "a\n*x" [Event.useAlias "x"] := ⟨2, readAlias⟩

/-- Candidate local repair obligation: the spurious second bare document cannot
be an explicit document. If checked, this shows that changing the continuation
arm's document premise to the explicit form excludes this witness; it is not a
global uniqueness or completeness theorem. -/
lemma alias_not_explicit (ev : List Event) : ¬ TLExplicitDocument u2 u4 ev := by
  intro h
  cases h with
  | withContent =>
    rename_i hmarker _
    cases hmarker

lemma plain_check_true : checkFrom {} ([] : List Event) = true := rfl
lemma alias_check_false : checkFrom {} [Event.useAlias "x"] = false := rfl

/-- Even the weaker, answer-relative transport condition fails on this grammar. -/
lemma answer_determinism_refuted :
    ¬ (∀ (input : String) (ev₁ ev₂ : List Event),
      TraceOf input ev₁ → TraceOf input ev₂ →
      checkFrom {} ev₁ = checkFrom {} ev₂) := by
  intro h
  have hbad := h "a\n*x" [] [Event.useAlias "x"] traceOf_plain traceOf_alias
  change true = false at hbad
  cases hbad

lemma plain_wellFormed : SerializationWellFormed ([] : List Event) := trivial

lemma alias_not_wellFormed : ¬ SerializationWellFormed [Event.useAlias "x"] := by
  simp [SerializationWellFormed, WellFormedFrom, AliasAllowed]

/-- A concrete source witness makes the current universal predicate false. -/
lemma traceWellFormed_false : ¬ TraceWellFormed "a\n*x" := by
  intro h
  exact alias_not_wellFormed (h _ traceOf_alias)

def parserAccepts (input : String) : Bool :=
  (TokenParser.parseYaml input).toOption.isSome

/-- Pending runtime control: expected acceptance of the single plain scalar. -/
lemma runtime_accepts : parserAccepts "a\n*x" = true := by native_decide

lemma runtime_acceptance : ∃ docs, TokenParser.parseYaml "a\n*x" = .ok docs := by
  have h := runtime_accepts
  cases hr : TokenParser.parseYaml "a\n*x" with
  | error e =>
    change (TokenParser.parseYaml "a\n*x").toOption.isSome = true at h
    rw [hr] at h
    change false = true at h
    cases h
  | ok docs => exact ⟨docs, rfl⟩

/-- This is the consequential failure, not only a difference between traces. -/
lemma acceptance_implies_traceWellFormed_refuted :
    ¬ (∀ input, (∃ docs, TokenParser.parseYaml input = .ok docs) →
      TraceWellFormed input) := by
  intro h
  exact traceWellFormed_false (h "a\n*x" runtime_acceptance)

-- Positive/negative controls localize the change to plain-scalar continuation.
#guard parserAccepts "a\n*x" = true
#guard parserAccepts "*x" = false
#guard parserAccepts "a\n---\n*x" = false
#guard parserAccepts "a\n&x" = true

#eval ("plain continuation", parserAccepts "a\n*x")
#eval ("standalone undeclared alias", parserAccepts "*x")
#eval ("marked next-document alias", parserAccepts "a\n---\n*x")
#eval ("known trace-inequality control", parserAccepts "a\n&x")

end

end MathGraph.TraceAnswerAudit

#print axioms MathGraph.TraceAnswerAudit.traceOf_plain
#print axioms MathGraph.TraceAnswerAudit.traceOf_alias
#print axioms MathGraph.TraceAnswerAudit.alias_not_explicit
#print axioms MathGraph.TraceAnswerAudit.answer_determinism_refuted
#print axioms MathGraph.TraceAnswerAudit.traceWellFormed_false
#print axioms MathGraph.TraceAnswerAudit.runtime_acceptance
#print axioms MathGraph.TraceAnswerAudit.acceptance_implies_traceWellFormed_refuted
