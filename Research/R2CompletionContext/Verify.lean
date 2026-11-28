import Lean

open Lean

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def readLog (name : String) : IO String := do
  let path := "Research/R2CompletionContext/logs/" ++ name ++ ".log.xz.b64"
  let result ← IO.Process.output {cmd := "bash", args := #["-c",
    "set -euo pipefail; base64 --decode \"$1\" | xz --decompress --stdout", "r2-completion-log", path]}
  require (result.exitCode == 0) s!"cannot decode {path}"
  pure result.stdout

def countField (line key : String) : IO Nat := do
  let some field := (line.splitOn " ").find? (·.startsWith (key ++ "="))
    | throw (IO.userError s!"missing counter {key}")
  let some n := (field.splitOn "=").getLast!.toNat?
    | throw (IO.userError s!"invalid counter {key}")
  pure n

def main : IO Unit := do
  let root := "Research/R2CompletionContext/"
  let audited ← readLog "audited"
  let erased ← readLog "erased"
  for variant in ["audited","erased"] do
    let status ← IO.FS.readFile (root ++ "logs/" ++ variant ++ ".exit")
    require (status.trimAscii.toString == "1") s!"wrong rejection boundary {variant}"
  let labels := #["R2_NODE_KEYLESS_COLON_ANCESTORS","R2_NODE_QUESTION_ANCESTORS",
    "R2_NODE_IMPLICIT_COLON_NO_TAIL","R2_NODE_IMPLICIT_COLON_ANCESTORS",
    "R2_NODE_PROPS_COLON_NO_TAIL","R2_NODE_PROPS_COLON_ANCESTORS",
    "R2_SEQUENCE_LANDED_LEFT_OF_SLOT","R2_SEQUENCE_LANDED_MISSING_SLOT",
    "R2_WHOLE_COMPACT_VALUE_SLOT","R2_WHOLE_LANDED_SEQUENCE"]
  let errors := (audited.splitOn "\n").filter (·.contains ": error")
  require (errors.length == 10) s!"audited errors {errors.length}"
  let erasedErrors := (erased.splitOn "\n").filter (·.contains ": error")
  require (erasedErrors.length == 11) s!"erased errors {erasedErrors.length}"
  for label in labels do
    require ((errors.filter (·.contains label)).length == 1) s!"audited residual {label}"
    require ((erasedErrors.filter (·.contains label)).length == 1) s!"erased residual {label}"
  let additional := erasedErrors.filter (fun e => !labels.any (fun label => e.contains label))
  require (additional.length == 1 && ((additional.head!).contains "Type mismatch" ||
    (additional.head!).contains "Application type mismatch")) "reader erasure is not one type mismatch"
  require (audited.contains "MANDATORY-CONTEXT-AUDIT actual_writers=8 supplied=6 residual=2") "six actual initializers not funded"
  require (erased.contains "MANDATORY-CONTEXT-AUDIT actual_writers=8 supplied=4 residual=4") "reader erasure did not affect actual field terms"
  let some auditLine := (audited.splitOn "\n").find? (·.startsWith "COMPLETION-CONTEXT-AUDIT completed_terms=")
    | throw (IO.userError "actual completion audit absent")
  let completed ← countField auditLine "completed_terms"
  let properties ← countField auditLine "property_context_writes"
  require (completed == 6 && properties == 3) "actual writer inventory changed"
  require (auditLine.contains "sorry_terms=0 actual_sibling_reader=connected") "unclean/disconnected completion"
  let result := Json.mkObj [
    ("state",toJson "WARRANTED_LOCAL_COMPLETION_SUPPLY; UNKNOWN_FULL_MIGRATION"),
    ("parent",toJson "b26c9bfd3e07b54f5b9bf74a7f3f4397e543cf7a"),
    ("parent_source_sha256",toJson "f4898e17ca902b360e8801650d3588e8c73511dd04003549f7ff0ff9921ca3d5"),
    ("audited_source_sha256",toJson "8e2bd5004d77c7acb59aedfdcab6e54059b2d39f6df4b55d7c36d7fd9581984b"),
    ("erased_source_sha256",toJson "1193ca6b16aba89c2e848a1ec30076a4aba50e6a9921753bba282d94d5fed710"),
    ("full_module_accepted",toJson false),
    ("actual_sequence_field_terms",toJson (8 : Nat)),
    ("actual_sequence_initializers_supplied",toJson (6 : Nat)),
    ("completed_field_terms_checked",toJson completed),
    ("property_context_writes_checked",toJson properties),
    ("remaining_diagnostic_labels",toJson labels),
    ("funded_existing_supplier",toJson "R2_WHOLE_COMPLETED_SEQUENCE"),
    ("replacement_failure_labels",toJson (0 : Nat)),
    ("extra_unlabelled_errors",toJson (0 : Nat)),
    ("erasure_additional_type_errors",toJson (1 : Nat)),
    ("earlier_erasure_resource_exit",toJson (137 : Nat)),
    ("earlier_erasure_resource_verdict",toJson "UNKNOWN_NO_LEAN_VERDICT"),
    ("missing_timing_utility_exit",toJson (127 : Nat)),
    ("constructor_fields_added",toJson (0 : Nat)),
    ("separate_context_parameters_added",toJson (0 : Nat)),
    ("existing_fields_strengthened",toJson ["pendingBlockContent.h_closable_entry","pendingProps.h_routeE"]),
    ("critical_retirements",toJson (0 : Nat)),
    ("full_repository_qualification",toJson "NOT_RUN"),
    ("clean_retirement_lane_integration",toJson "NOT_RUN"),
    ("new_finite_examples_promoted",toJson (0 : Nat)),
    ("production_pr_ready",toJson false)]
  IO.FS.writeFile (root ++ "result.json") (result.pretty ++ "\n")
  IO.println s!"VERIFIED actual_sequence_initializers=6/8 completed_terms={completed} property_context_writes={properties} remaining_labels=10 replacements=0 erasure_extra_type_errors=1 critical_retirements=0"
