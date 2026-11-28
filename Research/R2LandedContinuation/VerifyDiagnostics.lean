import Lean

open Lean

def readEvidence (path : System.FilePath) : IO String := do
  if ← path.pathExists then return ← IO.FS.readFile path
  let result ← IO.Process.output { cmd := "xz", args := #["-dc", path.toString ++ ".xz"] }
  unless result.exitCode == 0 do throw (IO.userError s!"cannot read evidence {path}")
  return result.stdout

def messages (text : String) : Array String :=
  text.splitOn "\n" |>.filterMap (fun line =>
    match line.splitOn ": error: " with
    | [_prefix, error] => some error
    | _ => none) |>.toArray

def rawArrayAfter (text marker : String) : IO String := do
  let parts := text.splitOn marker
  unless parts.length == 2 do throw (IO.userError s!"nonunique marker {marker}")
  let array := (parts[1]!.splitOn "]").head! ++ "]"
  unless array.startsWith "#[" do throw (IO.userError s!"missing array {marker}")
  return array

def main : IO Unit := do
  let parent ← readEvidence "Research/R2ContinuationContract/logs/marked-pair-diagnostic.log"
  let roster := messages parent
  unless roster.size == 22 do throw (IO.userError "wrong frozen parent roster")
  let expected := roster.filter (· != "R2_SEQUENCE_LANDED_FAMILY") ++
    #["R2_SEQUENCE_LANDED_LEFT_OF_SLOT", "R2_SEQUENCE_LANDED_MISSING_SLOT"]
  unless expected.size == 23 do throw (IO.userError "missing parent landed label")
  let logRoot := "Research/R2LandedContinuation/logs/"
  let positive ← readEvidence (logRoot ++ "producer-positive.log")
  let actual := messages positive
  unless actual.size == expected.size && actual.all expected.contains && expected.all actual.contains do
    throw (IO.userError s!"unexpected positive diagnostics {actual}")
  IO.println "LANDED-PRODUCER informative_arm=typed missing_slot=UNKNOWN left_of_slot=UNKNOWN labelled_errors=23 extra_errors=0"
  for marker in ["RAW-PRODUCER-AXIOMS ", "RAW-COMPACT-AXIOMS ", "RAW-SEQUENCE-COMPLETION-AXIOMS "] do
    unless (← rawArrayAfter parent marker) == (← rawArrayAfter positive marker) do
      throw (IO.userError s!"inherited axiom profile changed {marker}")
  IO.println "INHERITED-PROFILES mapping_value=true compact=true ordinary_completion=true byte_identical=true"
  let erased ← readEvidence (logRoot ++ "producer-erased.log")
  let errors := messages erased
  unless errors.size == expected.size + 1 && expected.all errors.contains &&
      (errors.filter (·.startsWith "Type mismatch")).size == 1 do
    throw (IO.userError s!"unexpected actual erasure diagnostics {errors}")
  let mismatchParts := erased.splitOn ": error: Type mismatch\n"
  unless mismatchParts.length == 2 do
    throw (IO.userError "nonunique erasure mismatch")
  let mismatch := (mismatchParts[1]!.splitOn "L4YAML/").head!
  unless (mismatch.splitOn "wide endPos content).left").length == 2 &&
      (mismatch.splitOn "SLYamlStream sp_start endPos").length == 2 &&
      (mismatch.splitOn "EntryValues ").length == 2 do
    throw (IO.userError "erasure did not fail at the actual saved-slot projection")
  let negative ← readEvidence (logRoot ++ "erased-reader.log")
  unless (messages negative).size == 1 && (negative.splitOn "payload").length >= 2 &&
      (negative.splitOn "SlotValues").length >= 2 do
    throw (IO.userError "standalone erased-reader control did not fail at payload")
  IO.println "ERASURE actual_producer=failed_at_stream_projection standalone_reader=failed_at_stream_slot controls=2/2"
  let audit ← readEvidence (logRoot ++ "Research-R2LandedContinuation-DependencyAudit.log")
  unless (audit.splitOn "nonempty_tail=true standard_axioms_only=true").length == 2 do
    throw (IO.userError "missing complete nonempty-tail dependency audit")
  IO.println "WARRANT landed_family=true initialized_two_ancestors=true nonempty_current_tail=true full_migration=UNKNOWN critical_retirements=0"
