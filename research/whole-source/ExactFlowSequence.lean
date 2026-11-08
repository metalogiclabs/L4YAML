module

public import ExactPlain
public meta import Lean

/-! Group 7.7 source syntax for scalar and recursive sequence arms of YAML
1.2.2 [136]–[139]. Separation uses [75]–[81] and the exact break and
comment character classes. Flow pairs, mappings, aliases and node
properties remain outside this fragment. The definition does not call the
scanner or parser. The consumer lemmas below it connect owned delimiters
to the existing plain scalar scanner bridge. -/

set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactFlowSequence

open L4YAML L4YAML.Surface L4YAML.Scanner L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open MathGraph.WholeSource.ExactLexical (CommentText)
open MathGraph.WholeSource.ExactQuoted
open MathGraph.WholeSource.ExactPlain

abbrev CommentEnd := GAlt Break (fun s t => s.chars = [] ∧ s = t)
abbrev SeparatedComment := GSeq SSeparateInLine (GOpt CommentText)
abbrev CommentLine := GSeq SeparatedComment CommentEnd
abbrev CommentLines :=
  GSeq (GAlt (GSeq (GOpt SeparatedComment) CommentEnd)
    (fun s t => s.col = 0 ∧ s = t)) (GStar CommentLine)
abbrev SeparateLines (n : Nat) := GAlt (GSeq CommentLines (SFlowLinePrefix n)) SSeparateInLine

def Separate (n : Nat) (ctx : YamlContext) : SurfPos → SurfPos → Prop :=
  match ctx with
  | .flowIn | .flowOut | .blockIn | .blockOut => SeparateLines n
  | .flowKey | .blockKey => SSeparateInLine

def SequenceContext (ctx : YamlContext) : Prop :=
  match ctx with
  | .flowIn | .flowOut | .flowKey | .blockKey => True
  | .blockIn | .blockOut => False

def inner (ctx : YamlContext) : YamlContext :=
  match ctx with
  | .blockKey | .flowKey => .flowKey
  | _ => .flowIn

mutual
  inductive Node (n : Nat) : YamlContext → SurfPos → SurfPos → Prop where
    | plain {ctx s t} : Plain n ctx s t → Node n ctx s t
    | single {ctx s t} : SingleQuoted n ctx s t → Node n ctx s t
    | double {ctx s t} : DoubleQuoted n ctx s t → Node n ctx s t
    | sequence {ctx s openEnd first t} :
        SequenceContext ctx → GLit '[' s openEnd →
        GOpt (Separate n ctx) openEnd first → Body n (inner ctx) first t →
        Node n ctx s t

  /-- The closing bracket is part of the body. The empty arm is used at the
  start and after a comma. Only an entry can expose a comma. -/
  inductive Body (n : Nat) : YamlContext → SurfPos → SurfPos → Prop where
    | close {ctx s t} : GLit ']' s t → Body n ctx s t
    | entry {ctx s contentEnd delimiter t} :
        Node n ctx s contentEnd → GOpt (Separate n ctx) contentEnd delimiter →
        AfterEntry n ctx delimiter t → Body n ctx s t

  inductive AfterEntry (n : Nat) : YamlContext → SurfPos → SurfPos → Prop where
    | close {ctx s t} : GLit ']' s t → AfterEntry n ctx s t
    | comma {ctx s commaEnd first t} :
        GLit ',' s commaEnd → GOpt (Separate n ctx) commaEnd first →
        Body n ctx first t → AfterEntry n ctx s t
end

lemma after_entry_indicator {n : Nat} {ctx : YamlContext} {delimiter t : SurfPos}
    (h : AfterEntry n ctx delimiter t) :
    ∃ c rest, delimiter.chars = c :: rest ∧ (c = ',' ∨ c = ']') := by
  cases h with
  | close h => cases h; exact ⟨_, _, rfl, Or.inr rfl⟩
  | comma h _ _ => cases h; exact ⟨_, _, rfl, Or.inl rfl⟩

lemma key_separation_whites {n : Nat} {s t : SurfPos}
    (h : GOpt (Separate n .flowKey) s t) : GStar SSWhite s t := by
  cases h with
  | none => exact .nil _
  | some _ h =>
    change SSeparateInLine _ _ at h
    cases h with
    | whites _ _ h => cases h; exact .cons _ _ _ ‹SSWhite _ _› ‹GStar SSWhite _ _›
    | startOfLine => exact .nil _

/-- The parent continuation supplies the scanner's indicator premise.
For key entries, the grammar also supplies the horizontal separation
via key_separation_whites. Flow value entries may use the same consumer
when their separator is horizontal. -/
lemma scan_plain_before_after_entry (sc : ScannerState) {n : Nat} {ctx : YamlContext}
    {s contentEnd delimiter t : SurfPos}
    (hCtx : ctx = .flowIn ∨ ctx = .flowKey)
    (hCorr : ScannerSurfCorr sc s) (hFlow : sc.inFlow = true)
    (hSpan : SNsPlainOneLine ctx s contentEnd)
    (hWhite : GStar SSWhite contentEnd delimiter)
    (hAfter : AfterEntry n ctx delimiter t)
    (hDoc : sc.col = 0 → atDocumentBoundary sc = false) :
    ∃ next value, scanPlainScalar sc = .ok next ∧ ScannerSurfCorr next delimiter ∧
      next.tokens = sc.tokens.push {pos := sc.currentPos, val := .scalar value .plain} := by
  apply scan_flow_plain_to_indicator sc hCtx hCorr hFlow hSpan hWhite _ hDoc
  obtain ⟨c, rest, hc, rfl | rfl⟩ := after_entry_indicator hAfter
  · exact ⟨_, _, hc, by decide⟩
  · exact ⟨_, _, hc, by decide⟩

end MathGraph.WholeSource.ExactFlowSequence
