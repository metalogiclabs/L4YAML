/-
# Seven-byte input: *positive* annotated-grammar derivation experiment

Hypothesis: the actual `TLYamlStream.implicitContinue` constructor may parse
"? -\\n  :" as TWO bare documents, with no separating document marker,
despite the native token parser refusing the bytes. The formal grammar
might therefore be broader than the external YAML language.

No production, lemma statement or scanner behavior is changed.
If this proof succeeds, the bare-string grammar *nonmembership* hypothesis is
REJECTED. It does NOT automatically prove that the extended directive-bearing
scanner event trace is in TraceOf, nor that the two-document interpretation
is authorized by YAML 1.2.2.
-/
module
public import L4YAML.Proofs.Serialization.TraceOf.Document
@[expose] public section Blanket

namespace L4YAML.Tests.Guards.ColonTwoBareDocuments
open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.TraceOf

def p0 : SurfPos := ⟨['?', ' ', '-', '\n', ' ', ' ', ':'], 0⟩
def p1 : SurfPos := ⟨[' ', '-', '\n', ' ', ' ', ':'], 1⟩
def p2 : SurfPos := ⟨['-', '\n', ' ', ' ', ':'], 2⟩
def p3 : SurfPos := ⟨['\n', ' ', ' ', ':'], 3⟩
def p4 : SurfPos := ⟨[' ', ' ', ':'], 0⟩
def p5 : SurfPos := ⟨[':'], 2⟩
def p6 : SurfPos := ⟨[], 3⟩

/-- The compact-sequence key reaches precisely the next line's two spaces.
Its child is empty; it cannot absorb the ':' at index 2. -/
lemma initial_key : TBlockIndented 0 .blockOut p1 p4 [] := by
  have hIndent : SIndent 1 p1 p2 := by
    exact SIndent.succ 0 ['-', '\n', ' ', ' ', ':'] 1 _ (.zero _)
  have hDash : GLit '-' p2 p3 := .mk ['\n', ' ', ' ', ':'] 2
  have hNoChar : GNot SNsChar p3 := by
    intro s h
    cases h with
    | mk c cs col hn =>
      exact hn.1 (by decide)
  have hComment : SSLComments p3 p4 := by
    apply SSLComments.withComment p3 p4 p4
    · exact SSBComment.noSep p3 p4
        (SBComment.break p3 p4 (.lf [' ', ' ', ':'] 3))
    · exact .nil p4
  have hEmpty : TBlockIndented 2 .blockIn p3 p4 [] :=
    TBlockIndented.empty 2 .blockIn p3 p4 hComment
  have hCompact : TCompactSeq 2 p2 p4 [] :=
    TCompactSeq.mk 2 p2 p3 p4 p4 [] []
      hDash hNoChar hEmpty (.nil 2 p4)
  exact TBlockIndented.compactSeq 0 .blockOut 1 p1 p2 p4 []
    hIndent hCompact

/-- First document: a key-only explicit block mapping. -/
lemma first_bare : TLBareDocument p0 p4 [] := by
  have hKey : TBlockMapEntry 0 p0 p4 [] :=
    .explicitEmpty 0 p0 p1 p4 [] (.mk [' ', '-', '\n', ' ', ' ', ':'] 0) initial_key
  have hEntries : TBlockMapEntries 0 p0 p4 [] :=
    .single 0 p0 p0 p4 [] (.zero p0) hKey
  have hNode : TBlockNode 0 .blockIn p0 p4 [] :=
    .blockMap 0 .blockIn 0 p0 p0 p0 p4 [] []
      (.none p0) (.startOfLine p0.chars p0 (.nil p0)) hEntries
  exact .mk p0 p4 [] hNode

/-- Second document: a two-indented empty-key mapping at EOF. -/
lemma second_bare : TLBareDocument p4 p6 [] := by
  have hIndent : SIndent 2 p4 p5 := by
    exact SIndent.succ 1 [' ', ':'] 0 _
      (SIndent.succ 0 [':'] 1 _ (.zero _))
  have hColon : GLit ':' p5 p6 := .mk [] 2
  have hEof : SSLComments p6 p6 :=
    .withComment p6 p6 p6
      (.noSep p6 p6 (.eof 3)) (.nil p6)
  have hEntry : TBlockMapEntry 2 p5 p6 [] :=
    .emptyKeyEmpty 2 p5 p6 p6 hColon hEof
  have hEntries : TBlockMapEntries 2 p4 p6 [] :=
    .single 2 p4 p5 p6 [] hIndent hEntry
  have hNode : TBlockNode 0 .blockIn p4 p6 [] :=
    .blockMap 0 .blockIn 2 p4 p4 p4 p6 [] []
      (.none p4) (.startOfLine p4.chars p4 (.nil p4)) hEntries
  exact .mk p4 p6 [] hNode

/-- IMPORTANT: the actual `TLYamlStream.implicitContinue` requires
`TOpt TLExplicitDocument`, NOT a second `TLAnyDocument.bare`.
Although each half has a bare-document derivation, that does not
license an implicit two-bare-document stream. -/
lemma no_explicit_second_document (ev : List L4YAML.Proofs.Serialization.SerializationWellFormed.Event) :
    ¬ TLExplicitDocument p4 p6 ev := by
  intro h
  cases h with
  | withContent _ _ _ _ hMarker _ =>
    cases hMarker

/-- No implicit continuation can reinterpret the colon line as another
bare document via the actual explicit-document-only arm. -/
lemma no_explicit_optional_second (ev : List L4YAML.Proofs.Serialization.SerializationWellFormed.Event) :
    ¬ TOpt TLExplicitDocument p4 p6 ev := by
  intro h
  cases h with
  | some s s' e hDoc =>
    exact no_explicit_second_document _ hDoc

/-- REMAINING TARGET (not promoted): rule out or construct the *whole*
annotated TLYamlStream over the source with marker and directive. -/
def FullStreamQuestion : Prop :=
  ∀ ev, ¬ TraceOf "? -\\n  :\\n...\\n%YAML 1.2\\n---\\ny" ev

#print axioms L4YAML.Tests.Guards.ColonTwoBareDocuments.initial_key
#print axioms L4YAML.Tests.Guards.ColonTwoBareDocuments.first_bare
#print axioms L4YAML.Tests.Guards.ColonTwoBareDocuments.second_bare
#print axioms L4YAML.Tests.Guards.ColonTwoBareDocuments.no_explicit_second_document
#print axioms L4YAML.Tests.Guards.ColonTwoBareDocuments.no_explicit_optional_second

end L4YAML.Tests.Guards.ColonTwoBareDocuments
end Blanket
