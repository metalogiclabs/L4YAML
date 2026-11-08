module
public import DirectiveDiscipline
public import L4YAML.Proofs.Serialization.EventsOf
public meta import Lean

/-! Source-retained directive multiplicity, YAML 1.2.2 §6.8.1–2.
This is a necessary condition, NOT complete directive syntax or a full language.
It refines the existing skeleton without replacing it or calling the parser.
In particular, primary/secondary explicit TAG declarations must be counted even
though EventsOf.declaredHandle intentionally omits them from availability events.
-/
@[expose] public section
namespace MathGraph.WholeSource.DirectiveRecords
open L4YAML.Proofs.Serialization.EventsOf
open L4YAML.Proofs.Serialization.SourceEvents
open MathGraph.WholeSource.DirectiveDiscipline

/-- Read an explicit TAG handle from retained source. Syntax validity remains
an independent obligation: this recognizer deliberately does not certify it. -/
def explicitTagHandle : List Char → Option (List Char)
  | '%' :: 'T' :: 'A' :: 'G' :: c :: cs =>
      if c == ' ' || c == '\t' then
        some ((dropHSpace cs).takeWhile fun x =>
          !(x == ' ' || x == '\t' || x == '\r' || x == '\n'))
      else none
  | _ => none

def DirectiveMultiplicity (dirs : List (List Char)) : Prop :=
  (dirs.filter isYamlDirectiveLine).length ≤ 1 ∧
  (dirs.filterMap explicitTagHandle).Nodup

def SegmentMultiplicity : Seg → Prop
  | .docStart dirs => DirectiveMultiplicity dirs
  | _ => True

def StreamMultiplicity (segs : List Seg) : Prop :=
  ∀ seg ∈ segs, SegmentMultiplicity seg

def DisciplinedSkeleton (col : Nat) (chars : List Char) (segs : List Seg) : Prop :=
  Skeleton col chars segs ∧ StreamMultiplicity segs

lemma source_preserved {col chars segs} (h : DisciplinedSkeleton col chars segs) :
    segs.flatMap Seg.text = chars := skeleton_text col chars segs h.1

/-- Multiplicity resets at each document: it is not a global handle uniqueness
condition. This law does not assert that arbitrary segment concatenation is
syntactically valid; Skeleton remains separately required. -/
lemma multiplicity_append (a b : List Seg) :
    StreamMultiplicity (a ++ b) ↔ StreamMultiplicity a ∧ StreamMultiplicity b := by
  simp [StreamMultiplicity, List.mem_append, or_imp, forall_and]

def primary : List Char := "%TAG ! x\n".toList
def secondary : List Char := "%TAG !! tag:x\n".toList
def named : List Char := "%TAG !h! tag:x\n".toList

/-- The collision's primary directive is genuinely admitted by the existing
surface grammar, before any original-source tail. -/
lemma primary_line (rest : List Char) :
    L4YAML.Surface.SLDirective ⟨primary ++ rest, 0⟩ ⟨rest, 0⟩ := by
  refine .tag (' ' :: '!' :: ' ' :: 'x' :: '\n' :: rest) 0
    ⟨'!' :: ' ' :: 'x' :: '\n' :: rest, 5⟩
    ⟨' ' :: 'x' :: '\n' :: rest, 6⟩
    ⟨'x' :: '\n' :: rest, 7⟩ ⟨'\n' :: rest, 8⟩ ⟨rest, 0⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t h
    cases h with
    | mk _ _ _ hp => exact hp.2.1 (by decide)
  · exact .cons _ _ _ (.space _ 4) (.nil _)
  · exact .cons _ _ _ (.mk '!' _ 5 (Or.inr rfl)) (.nil _)
  · intro t h
    cases h with
    | mk _ _ _ hp =>
      rcases hp with hp | hp
      · simp [L4YAML.CharPredicates.isWordCharProp,
          L4YAML.CharPredicates.isAsciiLetterProp] at hp
      · cases hp
  · exact .cons _ _ _ (.space _ 6) (.nil _)
  · exact .cons _ _ _ (.mk 'x' _ 7 (by decide)) (.nil _)
  · exact .withComment _ _ _ (.noSep _ _ (.break _ _ (.lf rest 8))) (.nil _)

lemma primary_skeleton (dirs : List (List Char))
    (hdirs : ∀ d ∈ dirs, d = primary) :
    Skeleton 0 ((Seg.docStart dirs).text) [.docStart dirs] := by
  have hat : SegAt 0 (.docStart dirs) [] := by
    refine ⟨rfl, .mk [], ?_⟩
    intro d hd
    have he := hdirs d hd
    subst d
    exact ⟨⟨'\n', by decide, by decide⟩, [], primary_line []⟩
  have hn : Skeleton (colAfter 0 (Seg.docStart dirs).text) [] [] := .nil _
  simpa using (Skeleton.cons 0 (.docStart dirs) [] [] hat hn (by simp [Seg.isOther]))

lemma single_primary_allowed : DirectiveMultiplicity [primary] := by
  unfold DirectiveMultiplicity
  decide
lemma duplicate_primary_excluded : ¬ DirectiveMultiplicity [primary, primary] := by
  unfold DirectiveMultiplicity
  decide
lemma single_secondary_allowed : DirectiveMultiplicity [secondary] := by
  unfold DirectiveMultiplicity
  decide
lemma duplicate_secondary_excluded : ¬ DirectiveMultiplicity [secondary, secondary] := by
  unfold DirectiveMultiplicity
  decide
lemma single_named_allowed : DirectiveMultiplicity [named] := by
  unfold DirectiveMultiplicity
  decide
lemma duplicate_named_excluded : ¬ DirectiveMultiplicity [named, named] := by
  unfold DirectiveMultiplicity
  decide
lemma distinct_handles_allowed : DirectiveMultiplicity [primary, secondary, named] := by
  unfold DirectiveMultiplicity
  decide
lemma duplicate_version_excluded :
    ¬ DirectiveMultiplicity ["%YAML 1.2\n".toList, "%YAML 1.2\n".toList] := by
  unfold DirectiveMultiplicity
  decide

lemma primary_resets_per_document :
    StreamMultiplicity [.docStart [primary], .docStart [primary]] := by
  simp [StreamMultiplicity, SegmentMultiplicity, single_primary_allowed]

lemma primary_event_collision :
    eventsOfSegs [.docStart [primary]] = eventsOfSegs [.docStart [primary, primary]] := by
  decide

/-- No predicate of the EXISTING event projection can enforce this source
multiplicity condition, even restricted to source-connected Skeleton derivations. This does not
claim public parser rejection or full YAML validity of either source. -/
lemma multiplicity_does_not_factor_through_events :
    ¬ ∃ P : List L4YAML.Proofs.Serialization.SerializationWellFormed.Event → Prop, ∀ col chars segs, Skeleton col chars segs →
      (StreamMultiplicity segs ↔ P (eventsOfSegs segs)) := by
  rintro ⟨P, h⟩
  have hone : StreamMultiplicity [.docStart [primary]] := by
    simp [StreamMultiplicity, SegmentMultiplicity, single_primary_allowed]
  have hs₁ := primary_skeleton [primary] (by simp)
  have hs₂ := primary_skeleton [primary, primary] (by simp)
  have htwo := (h 0 _ _ hs₂).mpr
    (primary_event_collision ▸ (h 0 _ _ hs₁).mp hone)
  have bad : DirectiveMultiplicity [primary, primary] :=
    htwo (.docStart [primary, primary]) (by simp)
  exact duplicate_primary_excluded bad

open Lean Elab Command in
run_cmd do
  for n in [``primary_line, ``primary_skeleton, ``source_preserved, ``multiplicity_append, ``single_primary_allowed,
      ``duplicate_primary_excluded, ``single_secondary_allowed, ``duplicate_secondary_excluded,
      ``single_named_allowed, ``duplicate_named_excluded, ``distinct_handles_allowed,
      ``duplicate_version_excluded, ``primary_resets_per_document,
      ``primary_event_collision, ``multiplicity_does_not_factor_through_events] do
    let axs ← collectAxioms n
    unless (axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
      throwError "UNQUALIFIED {n}: {axs}"
    logInfo m!"DIRECTIVE_RECORD_AXIOMS {n}: {axs}"
end MathGraph.WholeSource.DirectiveRecords
