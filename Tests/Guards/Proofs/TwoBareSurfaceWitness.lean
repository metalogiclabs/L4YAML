module
public import L4YAML.Surface.Document
@[expose] public section Blanket
/-! Concrete, scannerDrop-free overacceptance in the source grammar.
YAML 1.2.2 [211] permits only explicit document continuation after an
unterminated first bare document. Source SLYamlStream.implicitContinue
instead permits SLAnyDocument.bare. This example uses only the ordinary
grammar constructors single and implicitContinue. No T trace refutation.
Seven-byte source: "? -\\n  :". -/
namespace L4YAML.Tests.Guards.TwoBareSurfaceWitness
open L4YAML L4YAML.Surface

def p0 : SurfPos := ⟨['?', ' ', '-', '\n', ' ', ' ', ':'], 0⟩
def p1 : SurfPos := ⟨[' ', '-', '\n', ' ', ' ', ':'], 1⟩
def p2 : SurfPos := ⟨['-', '\n', ' ', ' ', ':'], 2⟩
def p3 : SurfPos := ⟨['\n', ' ', ' ', ':'], 3⟩
def p4 : SurfPos := ⟨[' ', ' ', ':'], 0⟩
def p5 : SurfPos := ⟨[':'], 2⟩
def p6 : SurfPos := ⟨[], 3⟩

lemma first_bare : SLBareDocument p0 p4 := by
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
  have hEmpty : SBlockIndented 2 .blockIn p3 p4 :=
    .empty 2 .blockIn p3 p4 hComment
  have hCompact : SCompactSeq 2 p2 p4 :=
    .mk 2 p2 p3 p4 p4 hDash hNoChar hEmpty (.nil 2 p4)
  have hKey : SBlockMapEntry 0 p0 p4 :=
    .explicitEmpty 0 p0 p1 p4 (.mk [' ', '-', '\n', ' ', ' ', ':'] 0)
      (.compactSeq 0 .blockOut 1 p1 p2 p4 hIndent hCompact)
  have hEntries : SBlockMapEntries 0 p0 p4 :=
    .single 0 p0 p0 p4 (.zero p0) hKey
  have hNode : SBlockNode 0 .blockIn p0 p4 :=
    .blockMap 0 .blockIn 0 p0 p0 p0 p4 (.none p0)
      (.startOfLine p0.chars p0 (.nil p0)) hEntries
  exact .mk p0 p4 hNode

lemma second_bare : SLBareDocument p4 p6 := by
  have hIndent : SIndent 2 p4 p5 :=
    SIndent.succ 1 [' ', ':'] 0 _
      (SIndent.succ 0 [':'] 1 _ (.zero _))
  have hColon : GLit ':' p5 p6 := .mk [] 2
  have hEof : SSLComments p6 p6 :=
    .withComment p6 p6 p6 (.noSep p6 p6 (.eof 3)) (.nil p6)
  have hEntry : SBlockMapEntry 2 p5 p6 :=
    .emptyKeyEmpty 2 p5 p6 p6 hColon hEof
  have hEntries : SBlockMapEntries 2 p4 p6 :=
    .single 2 p4 p5 p6 hIndent hEntry
  have hNode : SBlockNode 0 .blockIn p4 p6 :=
    .blockMap 0 .blockIn 2 p4 p4 p4 p6 (.none p4)
      (.startOfLine p4.chars p4 (.nil p4)) hEntries
  exact .mk p4 p6 hNode

/-- An unseparated pair of individually grammatical bare documents
admitted by the current source SLYamlStream via implicitContinue,
without the scannerDrop escape. -/
lemma source_overaccepts_unseparated_bare_pair :
    SLYamlStream p0 p6 := by
  have first : SLYamlStream p0 p4 :=
    .single p0 p0 p4 p4 (.nil p0)
      (.some p0 p4 (.bare p0 p4 first_bare)) (.nil p4)
  exact .implicitContinue p0 p4 p4 p6 p6 first (.nil p4)
    (.some p4 p6 (.bare p4 p6 second_bare)) (.nil p6)

#print axioms L4YAML.Tests.Guards.TwoBareSurfaceWitness.first_bare
#print axioms L4YAML.Tests.Guards.TwoBareSurfaceWitness.second_bare
#print axioms L4YAML.Tests.Guards.TwoBareSurfaceWitness.source_overaccepts_unseparated_bare_pair
end L4YAML.Tests.Guards.TwoBareSurfaceWitness
end Blanket
