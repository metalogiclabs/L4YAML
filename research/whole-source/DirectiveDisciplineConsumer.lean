module

import DirectiveDiscipline
meta import DirectiveDiscipline

/-!
# Fixed source-side version-discipline consumer

This contract and its literal controls precede the candidate implementation.
Qualification requires official CI for the exact source commit. Nothing here
claims scanner correspondence, global trace agreement, or YAML completeness.
-/

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open MathGraph.WholeSource.DirectiveDiscipline

-- Literal expectations catch dropping a line, merging CR-separated lines,
-- counting the CRLF empty line, or requiring a final line break.
#guard countYamlDirectiveLines "".toList = 0
#guard countYamlDirectiveLines "%YAML 1.2\n".toList = 1
#guard countYamlDirectiveLines "%YAML 1.2\r".toList = 1
#guard countYamlDirectiveLines "%YAML 1.2\r\n".toList = 1
#guard countYamlDirectiveLines "%YAML 1.2\n%YAML 1.2\n".toList = 2
#guard countYamlDirectiveLines "%YAML 1.2\r%YAML 1.2\r".toList = 2
#guard countYamlDirectiveLines "%YAML 1.2\r\n%YAML 1.2\r\n".toList = 2
#guard countYamlDirectiveLines "%YAML 1.2".toList = 1
#guard countYamlDirectiveLines "%YAML 1.2\n%YAML 1.1".toList = 2
#guard countYamlDirectiveLines "%YAML\t1.2\r%YAML\t1.1".toList = 2
#guard countYamlDirectiveLines "%YAML".toList = 1
#guard countYamlDirectiveLines "\r\n\n\r".toList = 0

-- The name is the maximal isNsChar run following an initial '%'. These
-- controls catch prefix/substring searches and whitespace/comment trimming.
#guard countYamlDirectiveLines "%YAMLish 1.2\n".toList = 0
#guard countYamlDirectiveLines "%YAML#comment\n".toList = 0
#guard countYamlDirectiveLines "%FOO %YAML 1.2\n".toList = 0
#guard countYamlDirectiveLines "# %YAML 1.2\n".toList = 0
#guard countYamlDirectiveLines " %YAML 1.2\n".toList = 0
#guard countYamlDirectiveLines "\t%YAML 1.2\n".toList = 0
#guard countYamlDirectiveLines "%YAML 1.2 # %YAML 1.1\n".toList = 1
#guard countYamlDirectiveLines "%FOO %YAML 1.2\r\n# %YAML 1.1\r\n%YAML\t1.2".toList = 1
#guard countYamlDirectiveLines "%TAG !t! tag:x,2000:\n%TAG !t! tag:y,2000:\n".toList = 0

-- Pin the consumed source spans, including the unconsumed original suffix.
#guard countYamlDirectiveLines
  (span ⟨"%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩) = 1
#guard countYamlDirectiveLines
  (span ⟨"%YAML 1.2\n%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩) = 2

-- Non-vacuous preservation: a refined run is actually constructed, reusing
-- Task 1's exported source witness rather than a copied constructor proof.
example : VersionDisciplinedRun
    ⟨"%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩ [] :=
  run_one

-- This cannot be satisfied by merely excluding the previously chosen trace.
example : ∀ ev : List Event, ¬ VersionDisciplinedRun
    ⟨"%YAML 1.2\n%YAML 1.2\n---".toList, 0⟩ ⟨"---".toList, 0⟩ ev :=
  run_two_excluded

example {s t : SurfPos} {ev : List Event} (h : VersionDisciplinedRun s t ev) :
    TPlus TLDirective s t ev :=
  version_run_erases h

example {s t : SurfPos} {ev : List Event} (h : VersionDisciplinedRun s t ev) :
    countYamlDirectiveLines (span s t) ≤ 1 :=
  version_run_count_bound h

-- These new proof declarations must remain independent of imported Runtime
-- observations. The official receipts, not this source, determine profiles.
#print axioms MathGraph.WholeSource.DirectiveDiscipline.countYamlDirectiveLines
#print axioms MathGraph.WholeSource.DirectiveDiscipline.VersionDisciplinedRun
#print axioms MathGraph.WholeSource.DirectiveDiscipline.version_run_erases
#print axioms MathGraph.WholeSource.DirectiveDiscipline.version_run_count_bound
#print axioms MathGraph.WholeSource.DirectiveDiscipline.run_one
#print axioms MathGraph.WholeSource.DirectiveDiscipline.run_two_excluded
