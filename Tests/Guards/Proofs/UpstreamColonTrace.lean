/-
Exact upstream [211] admission experiment for Group 7.7.

Frozen library parent: 14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f.
The proof builds the seven actual bytes 3f 20 2d 0a 20 20 3a as two
bare documents. No scannerDrop, scanner acceptance premise, parser premise,
reflection, new axiom or change to the library grammar is used.

Dependency purpose: the Group 7.7 ExactSurfaceLanguage/TraceOf contract
must distinguish this upstream T grammar from the tighter research T grammar.
This is an admission witness, not a universal grammar nonmembership claim.
-/
module
public import L4YAML.Proofs.Serialization.TraceOf.Document
@[expose] public section Blanket

namespace L4YAML.Tests.Guards.UpstreamColonTrace
open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.SerializationWellFormed

def input : String := "? -\n  :"

-- Bind the experiment to bytes, including one actual line feed.
#guard input.utf8ByteSize == 7
#guard input.toList == ['?', ' ', '-', '\n', ' ', ' ', ':']

def p0 : SurfPos := ⟨['?', ' ', '-', '\n', ' ', ' ', ':'], 0⟩
def p1 : SurfPos := ⟨[' ', '-', '\n', ' ', ' ', ':'], 1⟩
def p2 : SurfPos := ⟨['-', '\n', ' ', ' ', ':'], 2⟩
def p3 : SurfPos := ⟨['\n', ' ', ' ', ':'], 3⟩
def p4 : SurfPos := ⟨[' ', ' ', ':'], 0⟩
def p5 : SurfPos := ⟨[':'], 2⟩
def p6 : SurfPos := ⟨[], 3⟩

lemma initial_key : TBlockIndented 0 .blockOut p1 p4 [] := by
  have hIndent : SIndent 1 p1 p2 :=
    SIndent.succ 0 ['-', '\n', ' ', ' ', ':'] 1 _ (.zero _)
  have hDash : GLit '-' p2 p3 := .mk ['\n', ' ', ' ', ':'] 2
  have hNoChar : GNot SNsChar p3 := by
    intro s h
    cases h with
    | mk c cs col hn => exact hn.1 (by decide)
  have hComment : SSLComments p3 p4 := by
    apply SSLComments.withComment p3 p4 p4
    · exact SSBComment.noSep p3 p4
        (SBComment.break p3 p4 (.lf [' ', ' ', ':'] 3))
    · exact .nil p4
  have hEmpty : TBlockIndented 2 .blockIn p3 p4 [] :=
    .empty 2 .blockIn p3 p4 hComment
  have hCompact : TCompactSeq 2 p2 p4 [] :=
    .mk 2 p2 p3 p4 p4 [] [] hDash hNoChar hEmpty (.nil 2 p4)
  exact .compactSeq 0 .blockOut 1 p1 p2 p4 [] hIndent hCompact

lemma first_bare : TLBareDocument p0 p4 [] := by
  have hKey : TBlockMapEntry 0 p0 p4 [] :=
    .explicitEmpty 0 p0 p1 p4 []
      (.mk [' ', '-', '\n', ' ', ' ', ':'] 0) initial_key
  have hEntries : TBlockMapEntries 0 p0 p4 [] :=
    .single 0 p0 p0 p4 [] (.zero p0) hKey
  have hNode : TBlockNode 0 .blockIn p0 p4 [] :=
    .blockMap 0 .blockIn 0 p0 p0 p0 p4 [] []
      (.none p0) (.startOfLine p0.chars p0 (.nil p0)) hEntries
  exact .mk p0 p4 [] hNode

lemma second_bare : TLBareDocument p4 p6 [] := by
  have hIndent : SIndent 2 p4 p5 :=
    SIndent.succ 1 [' ', ':'] 0 _
      (SIndent.succ 0 [':'] 1 _ (.zero _))
  have hColon : GLit ':' p5 p6 := .mk [] 2
  have hEof : SSLComments p6 p6 :=
    .withComment p6 p6 p6 (.noSep p6 p6 (.eof 3)) (.nil p6)
  have hEntry : TBlockMapEntry 2 p5 p6 [] :=
    .emptyKeyEmpty 2 p5 p6 p6 hColon hEof
  have hEntries : TBlockMapEntries 2 p4 p6 [] :=
    .single 2 p4 p5 p6 [] hIndent hEntry
  have hNode : TBlockNode 0 .blockIn p4 p6 [] :=
    .blockMap 0 .blockIn 2 p4 p4 p4 p6 [] []
      (.none p4) (.startOfLine p4.chars p4 (.nil p4)) hEntries
  exact .mk p4 p6 [] hNode

/-- Negative control: the second bare document has no explicit start marker. -/
lemma second_is_not_explicit (ev : List Event) :
    ¬ TLExplicitDocument p4 p6 ev := by
  intro h
  cases h with
  | withContent _ _ _ _ hMarker _ => cases hMarker

/-- The upstream annotated grammar admits both unseparated bare documents. -/
lemma annotated_stream_admits : TLYamlStream p0 p6 [] := by
  have first : TLYamlStream p0 p4 [] :=
    .single p0 p0 p4 p4 [] [] (.nil p0)
      (.some p0 p4 [] (.bare p0 p4 [] first_bare)) (.nil p4)
  exact .implicitContinue p0 p4 p4 p6 p6 [] [] [] first (.nil p4)
    (.some p4 p6 [] (.bare p4 p6 [] second_bare)) (.nil p6)

/-- Whole-input decision, with the actual string and EOF cursor. -/
lemma traceOf_seven_bytes : TraceOf input [] := by
  exact ⟨3, annotated_stream_admits⟩

-- Positive control independent of the nonempty construction.
example : TraceOf "" [] := traceOf_empty

#print axioms initial_key
#print axioms first_bare
#print axioms second_bare
#print axioms second_is_not_explicit
#print axioms annotated_stream_admits
#print axioms traceOf_seven_bytes

end L4YAML.Tests.Guards.UpstreamColonTrace
end Blanket
