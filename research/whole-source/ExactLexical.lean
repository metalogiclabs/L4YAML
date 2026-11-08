module
public import ExactCharacters
set_option autoImplicit false
@[expose] public section
namespace MathGraph.WholeSource.ExactLexical
open L4YAML.Surface MathGraph.WholeSource.ExactCharacters
/-! Group 7.7: source-only lexical relations for [75], [107], [118].
Normative source: YAML 1.2.2, blob 2f078ec32749a55b5ad961899ed0f344037260e0.
Hex escapes denote Unicode scalar values (5.7); Lean String cannot contain
surrogate code points. No production scanner/parser or acceptance import.
These are character/body relations, not full multiline/contextual scalars. -/
def NamedEscape (c : Char) : Prop :=
  c ∈ ['0', 'a', 'b', 't', '\t', 'n', 'v', 'f', 'r', 'e', ' ', '"', '/', '\\', 'N', '_', 'L', 'P']
def HexDigitValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if c >= 'a' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10
def HexValue (digits : List Char) : Nat :=
  digits.foldl (fun acc c => acc * 16 + HexDigitValue c) 0
instance (c : Char) : Decidable (NamedEscape c) := by unfold NamedEscape; infer_instance
inductive CommentText : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) (col : Nat) (s' : SurfPos) :
      GStar (GChar NbChar) ⟨rest, col + 1⟩ s' → CommentText ⟨'#' :: rest, col⟩ s'

inductive DoubleChar : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hJson : NbJson c) (hNotBs : c ≠ '\\') (hNotDq : c ≠ '"') :
      DoubleChar ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escape (ec : Char) (rest : List Char) (col : Nat)
      (hValid : NamedEscape ec) :
      DoubleChar ⟨'\\' :: ec :: rest, col⟩ ⟨rest, col + 2⟩
  | hexEscape2 (rest : List Char) (col : Nat) (h1 h2 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hVal : (HexValue [h1, h2]).isValidChar) :
      DoubleChar ⟨'\\' :: 'x' :: h1 :: h2 :: rest, col⟩ ⟨rest, col + 4⟩
  | hexEscape4 (rest : List Char) (col : Nat) (h1 h2 h3 h4 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4)
      (hVal : (HexValue [h1, h2, h3, h4]).isValidChar) :
      DoubleChar ⟨'\\' :: 'u' :: h1 :: h2 :: h3 :: h4 :: rest, col⟩ ⟨rest, col + 6⟩
  | hexEscape8 (rest : List Char) (col : Nat) (h1 h2 h3 h4 h5 h6 h7 h8 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4)
      (hHex5 : isNsHexDigit h5) (hHex6 : isNsHexDigit h6)
      (hHex7 : isNsHexDigit h7) (hHex8 : isNsHexDigit h8)
      (hVal : (HexValue [h1, h2, h3, h4, h5, h6, h7, h8]).isValidChar) :
      DoubleChar ⟨'\\' :: 'U' :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: rest, col⟩
        ⟨rest, col + 10⟩

inductive SingleChar : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hJson : NbJson c) (hNotSq : c ≠ '\'') :
      SingleChar ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escapedQuote (rest : List Char) (col : Nat) :
      SingleChar ⟨'\'' :: '\'' :: rest, col⟩ ⟨rest, col + 2⟩

-- Constituent character runs, not claims about complete scalar delimiters.
abbrev DoubleBody := GStar DoubleChar
abbrev SingleBody := GStar SingleChar
end MathGraph.WholeSource.ExactLexical
