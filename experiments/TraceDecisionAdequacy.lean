module

public import L4YAML
public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.ScannerShape
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

/-- `traceOf_unique` is FALSE as stated while `implicitContinue` admits a bare document. -/
lemma traceOf_unique_refuted_alias :
    ¬ (∀ (input : String) (ev₁ ev₂ : List Event),
        TraceOf input ev₁ → TraceOf input ev₂ → ev₁ = ev₂) :=
  fun h => by cases h _ _ _ traceOf_plain traceOf_alias

end ImplicitContinue
  
/-! ## Positive boundary: the event trace actually emitted by the scanner -/

-- This is a corollary of the *existing upstream* scanner/parser S5 theorem,
-- not a new upstream finding. It intentionally quantifies over the executed
-- scanner stream instead of every admissible surface-grammar derivation.
open L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.ScannerShape

lemma executedScannerTraceWellFormed
    (input : String) (ts : Toks) (docs : Array YamlDocument)
    (hs : scanFiltered input = .ok ts)
    (hp : parseStream ts = .ok docs) :
    SerializationWellFormed (tokenEvents ts) := by
  apply (serializationWellFormed_iff_check (tokenEvents ts)).mpr
  exact scanFiltered_parseStream_ok_checkFrom_full input ts docs hs hp

-- The public Load function composes parsed documents, but cannot accept
-- unless the source scanner and token parser have both succeeded.
lemma acceptedLoadHasWellFormedScannerTrace
    (input : String) (docs : Array YamlDocument)
    (hload : parseYaml input = .ok docs) :
    ∃ ts : Toks, scanFiltered input = .ok ts ∧
      SerializationWellFormed (tokenEvents ts) := by
  unfold parseYaml parseYamlRaw at hload
  cases hs : scanFiltered input with
  | error e => simp [hs] at hload
  | ok ts =>
    cases hp : parseStream ts with
    | error e => simp [hs, hp] at hload
    | ok rawDocs =>
      exact ⟨ts, hs, executedScannerTraceWellFormed input ts rawDocs hs hp⟩

/-! ## New requirement-relevant distinction -/
lemma emptyEventsWellFormed : SerializationWellFormed ([] : List Event) := by
  apply (serializationWellFormed_iff_check _).mpr
  decide

lemma undefinedAliasNotWellFormed :
    ¬ SerializationWellFormed [Event.useAlias "x"] := by
  intro h
  have hcheck := (serializationWellFormed_iff_check _).mp h
  have hbad : checkFrom ({} : Env) [Event.useAlias "x"] = false := by decide
  simp [hbad] at hcheck

lemma traceWellFormedRefuted : ¬ TraceWellFormed "a\n*x" := by
  intro h
  exact undefinedAliasNotWellFormed (h _ traceOf_alias)

-- A successful parser result would also refute parse-acceptance → TraceWellFormed.
#eval if (L4YAML.TokenParser.parseYaml "a\n*x").isOk then
  "SOURCE_PARSER_ACCEPT" else "SOURCE_PARSER_REJECT"
/-! ## Source-native parser qualification (evaluation, not kernel acceptance proof) -/

-- The same input must yield exactly one plain scalar whose folded content is "a *x".
#eval L4YAML.TokenParser.parseYamlSingle "a\n*x"
#eval (L4YAML.TokenParser.parseYaml "a\n*x").map (fun docs => docs.size)
#guard (match L4YAML.TokenParser.parseYamlSingle "a\n*x" with
  | .ok (.scalar s) => s.content == "a *x" && s.style == .plain
  | _ => false)
#guard (match L4YAML.TokenParser.parseYaml "a\n*x" with
  | .ok docs => docs.size == 1
  | .error _ => false)

-- A real document start marker changes the stream into two documents.
#eval (L4YAML.TokenParser.parseYaml "a\n---\nb").map (fun docs => docs.size)
#guard (match L4YAML.TokenParser.parseYaml "a\n---\nb" with
  | .ok docs => docs.size == 2
  | .error _ => false)
#guard (match L4YAML.TokenParser.parseYamlSingle "a\n---\nb" with
  | .error _ => true
  | _ => false)

-- Kernel dependencies of the Lean-checked trace refutation.
#print axioms traceOf_plain
#print axioms traceOf_alias
#print axioms undefinedAliasNotWellFormed
#print axioms traceWellFormedRefuted
#print axioms executedScannerTraceWellFormed
#print axioms acceptedLoadHasWellFormedScannerTrace
#check traceWellFormedRefuted

end L4YAML.Tests.Guards.TraceOfBlockAmbiguity
