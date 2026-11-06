module

public import DirectiveTrace
public meta import DirectiveTrace

/-!
# Source-side version uniqueness for an existing directive run

Candidate extension of research source
5e6c0d2ca2cc95d9aa56017d35e305f67350a2a4, over unchanged production source
64795a8db28ccfdae85082c93b6453001ae9d3e4. Official CI for the exact candidate
source is the qualification boundary; this file makes no passing claim.

This external Group 7.7 grammar-completeness audit refines `TPlus TLDirective`
with one independently source-derived condition on its existing consumed span.
It pays only version-name uniqueness in that span. It does not supply a
source-to-scanner simulation, actual-token correspondence, global trace
agreement, or a complete YAML-language characterization. Tag syntax and
duplicate TAG declarations remain separate; existing runtime controls accept
duplicate TAG declarations. No production grammar or runtime is changed.

The fixed consumer requires both preservation of the existing one-directive
original-source run and exclusion of the exact duplicate span for every event
list. The source witness is imported rather than reconstructed. The new
proofs use ordinary kernel reasoning, not the imported Runtime observations.
-/

namespace MathGraph.WholeSource.DirectiveDiscipline

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf

-- This computes the existing source character predicate; it does not call
-- any scanner/parser or introduce classical decidability.
private def isNsCharBool (c : Char) : Bool :=
  letI : Decidable (isNsChar c) := by
    unfold isNsChar
    infer_instance
  decide (isNsChar c)

/-- Split each CR and each LF separately. A CRLF therefore contributes an
extra empty physical line, whose directive count is zero. No trimming occurs. -/
private def physicalLines : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
      if c == '\r' || c == '\n' then
        [] :: physicalLines cs
      else
        match physicalLines cs with
        | [] => [[c]]
        | line :: lines => (c :: line) :: lines

/-- Recognize only an initial `%` followed by the maximal `isNsChar` name
exactly `YAML`. This is a name count, not validation of a version-line body. -/
private def isYamlDirectiveLine : List Char → Bool
  | '%' :: rest => rest.takeWhile isNsCharBool == ['Y', 'A', 'M', 'L']
  | _ => false

/-- Independent source-only count of physical lines with directive name YAML.
Reserved-directive bodies, comments, and indented `%YAML` text do not count.
A final unterminated physical line is included. -/
def countYamlDirectiveLines (chars : List Char) : Nat :=
  ((physicalLines chars).filter isYamlDirectiveLine).length

/-- The source-side version condition is on the same span as the existing
run. There is no ghost count index and no assumed scanner/parser success. -/
def VersionDisciplinedRun (s t : SurfPos) (ev : List Event) : Prop :=
  TPlus TLDirective s t ev ∧ countYamlDirectiveLines (span s t) ≤ 1

/-- Refinement erasure preserves the original run, endpoints, and events. -/
lemma version_run_erases {s t : SurfPos} {ev : List Event}
    (h : VersionDisciplinedRun s t ev) : TPlus TLDirective s t ev :=
  h.1

/-- The consumed source span, not an event-derived count, carries the bound. -/
lemma version_run_count_bound {s t : SurfPos} {ev : List Event}
    (h : VersionDisciplinedRun s t ev) :
    countYamlDirectiveLines (span s t) ≤ 1 :=
  h.2

/-- Non-vacuous preservation of Task 1's exact existing original-source run.
The original `---` suffix remains unconsumed in both endpoint descriptions. -/
lemma run_one : VersionDisciplinedRun
    ⟨"%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩ [] :=
  ⟨MathGraph.WholeSource.DirectiveTrace.one_directive_run, by decide⟩

/-- Exclude this exact duplicate source span independently of the event list
and of any choice of derivation for the old annotated directive relation. -/
lemma run_two_excluded (ev : List Event) : ¬ VersionDisciplinedRun
    ⟨"%YAML 1.2\n%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩ ev := by
  intro h
  have hnot : ¬ countYamlDirectiveLines
      (span ⟨"%YAML 1.2\n%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩) ≤ 1 := by
    decide
  exact hnot (version_run_count_bound h)

end

end MathGraph.WholeSource.DirectiveDiscipline
