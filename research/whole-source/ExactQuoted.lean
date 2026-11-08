module
public import ExactLexical
set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactQuoted
open L4YAML L4YAML.Surface MathGraph.WholeSource.ExactLexical
/-! Source-only translation of YAML 1.2.2 [108]-[116], [119]-[125].
Dependencies [28], [63]-[74] are represented explicitly or reused below.
Normative blob 2f078ec32749a55b5ad961899ed0f344037260e0.
This is syntax, not a decoded-value semantics or a runtime acceptance premise.
Document-level forbidden-marker conditions remain the stream grammar's duty. -/

/-- [28]: consume CRLF together; a lone CR cannot steal its LF. -/
inductive Break : SurfPos → SurfPos → Prop where
  | crlf (rest : List Char) (col : Nat) :
      Break ⟨'\r' :: '\n' :: rest, col⟩ ⟨rest, 0⟩
  | cr (rest : List Char) (col : Nat) (h : rest.head? ≠ some '\n') :
      Break ⟨'\r' :: rest, col⟩ ⟨rest, 0⟩
  | lf (rest : List Char) (col : Nat) :
      Break ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩

/-- [70] specialized to FLOW-IN: prefix or strictly less indentation, then break. -/
abbrev EmptyFlow (n : Nat) := GSeq (GAlt (SFlowLinePrefix n) (SIndentLt n)) Break
/-- [71] trimmed break followed by at least one empty line. -/
abbrev Trimmed (n : Nat) := GSeq Break (GPlus (EmptyFlow n))
/-- [73] b-l-folded: trimmed or space. No output folding semantics is asserted. -/
abbrev Folded (n : Nat) := GAlt (Trimmed n) Break
/-- [74] s-flow-folded. -/
abbrev FlowFolded (n : Nat) :=
  GSeq3 (GOpt SSeparateInLine) (Folded n) (SFlowLinePrefix n)

/-- [108], [119]: subtract raw whitespace, not escaped whitespace. -/
def DoubleNonSpace (s t : SurfPos) : Prop :=
  DoubleChar s t ∧ s.chars.head? ≠ some ' ' ∧ s.chars.head? ≠ some '\t'
def SingleNonSpace (s t : SurfPos) : Prop :=
  SingleChar s t ∧ s.chars.head? ≠ some ' ' ∧ s.chars.head? ≠ some '\t'
/-- [114], [123]. -/
abbrev DoubleInLine := GStar (GSeq (GStar SSWhite) DoubleNonSpace)
abbrev SingleInLine := GStar (GSeq (GStar SSWhite) SingleNonSpace)
/-- [112]: whitespace, escape, break, empty lines, next prefix. -/
inductive DoubleEscaped (n : Nat) : SurfPos → SurfPos → Prop where
  | mk (a b c d e f : SurfPos) :
      GStar SSWhite a b → GLit '\\' b c → Break c d →
      GStar (EmptyFlow n) d e → SFlowLinePrefix n e f → DoubleEscaped n a f
/-- [113]. -/
abbrev DoubleBreak (n : Nat) := GAlt (DoubleEscaped n) (FlowFolded n)

/-- [115], the optional continuation expanded into empty/last/more cases. -/
inductive DoubleNext (n : Nat) : SurfPos → SurfPos → Prop where
  | empty (a b : SurfPos) : DoubleBreak n a b → DoubleNext n a b
  | last (a b c d e : SurfPos) : DoubleBreak n a b → DoubleNonSpace b c →
      DoubleInLine c d → GStar SSWhite d e → DoubleNext n a e
  | more (a b c d e : SurfPos) : DoubleBreak n a b → DoubleNonSpace b c →
      DoubleInLine c d → DoubleNext n d e → DoubleNext n a e
/-- [124]. -/
inductive SingleNext (n : Nat) : SurfPos → SurfPos → Prop where
  | empty (a b : SurfPos) : FlowFolded n a b → SingleNext n a b
  | last (a b c d e : SurfPos) : FlowFolded n a b → SingleNonSpace b c →
      SingleInLine c d → GStar SSWhite d e → SingleNext n a e
  | more (a b c d e : SurfPos) : FlowFolded n a b → SingleNonSpace b c →
      SingleInLine c d → SingleNext n d e → SingleNext n a e
/-- [116], [125]. -/
abbrev DoubleMulti (n : Nat) := GSeq DoubleInLine (GAlt (DoubleNext n) (GStar SSWhite))
abbrev SingleMulti (n : Nat) := GSeq SingleInLine (GAlt (SingleNext n) (GStar SSWhite))
/-- [110], [121]. The spec has no BLOCK-IN/BLOCK-OUT alternatives here. -/
def DoubleText (n : Nat) (ctx : YamlContext) : SurfPos → SurfPos → Prop :=
  match ctx with
  | .flowIn | .flowOut => DoubleMulti n
  | .blockKey | .flowKey => DoubleBody
  | .blockIn | .blockOut => fun _ _ => False
def SingleText (n : Nat) (ctx : YamlContext) : SurfPos → SurfPos → Prop :=
  match ctx with
  | .flowIn | .flowOut => SingleMulti n
  | .blockKey | .flowKey => SingleBody
  | .blockIn | .blockOut => fun _ _ => False
/-- [109], [120]. -/
abbrev DoubleQuoted (n : Nat) (ctx : YamlContext) :=
  GSeq3 (GLit '"') (DoubleText n ctx) (GLit '"')
abbrev SingleQuoted (n : Nat) (ctx : YamlContext) :=
  GSeq3 (GLit '\'') (SingleText n ctx) (GLit '\'')
end MathGraph.WholeSource.ExactQuoted
