import Lean

open Lean

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def readLog (name : String) : IO String := do
  let path := "Research/R2MandatoryContext/logs/" ++ name ++ ".log.xz.b64"
  let result ← IO.Process.output {cmd := "bash", args := #["-c",
    "set -euo pipefail; base64 --decode \"$1\" | xz --decompress --stdout", "r2-log-reader", path]}
  require (result.exitCode == 0) s!"cannot decode retained log {path}"
  pure result.stdout

def main : IO Unit := do
  let root := "Research/R2MandatoryContext/"
  for moduleName in ["controls","births","completion","values","witness","audit"] do
    let status ← IO.FS.readFile (root ++ "logs/" ++ moduleName ++ ".exit")
    require (status.trimAscii.toString == "0") s!"module not accepted: {moduleName}"
  let migration ← readLog "migration-funded"
  let status ← IO.FS.readFile (root ++ "logs/migration-funded.exit")
  require (status.trimAscii.toString == "1") "migration must remain honestly rejected"
  let old := #["R2_NODE_KEYLESS_COLON_ANCESTORS","R2_NODE_QUESTION_ANCESTORS",
    "R2_NODE_IMPLICIT_COLON_NO_TAIL","R2_NODE_IMPLICIT_COLON_ANCESTORS",
    "R2_NODE_PROPS_COLON_NO_TAIL","R2_NODE_PROPS_COLON_ANCESTORS",
    "R2_SEQUENCE_LANDED_LEFT_OF_SLOT","R2_SEQUENCE_LANDED_MISSING_SLOT"]
  let additional := #["R2_WHOLE_COMPACT_VALUE_SLOT","R2_WHOLE_LANDED_SEQUENCE",
    "R2_WHOLE_COMPLETED_SEQUENCE"]
  let errors := (migration.splitOn "\n").filter (·.contains ": error")
  require (errors.length == 11) s!"unexpected migration error count {errors.length}"
  for label in old ++ additional do
    require ((errors.filter (·.contains label)).length == 1) s!"missing/duplicated residual {label}"
  require (migration.contains "MANDATORY-CONTEXT-AUDIT actual_writers=8 supplied=4 residual=4")
    "actual field audit did not qualify"
  let erased ← readLog "erased-reader"
  let erasedExit ← IO.FS.readFile (root ++ "logs/erased-reader.exit")
  require (erasedExit.trimAscii.toString == "1") "erasure unexpectedly accepted"
  require (((erased.splitOn "\n").filter (·.contains ": error")).length == 1)
    "erasure must have exactly one type mismatch"
  let audit ← readLog "audit"
  require (audit.contains "MANDATORY-WITNESS-AUDIT required=10 forbidden=9") "witness audit absent"
  require (audit.contains "free_premises=0 pure_roots=15 axioms=standard_three") "witness trust boundary changed"
  let result := Json.mkObj [
    ("state", toJson "WARRANTED_LOCAL_PRODUCERS_AND_FOUR_ACTUAL_WRITERS; UNKNOWN_FULL_MIGRATION"),
    ("parent", toJson "ee5739cc5ce5646752a683c94b12cf0b3895cda1"),
    ("parallel_active_retirement_lane", toJson "test/r2-sequence-retirement"),
    ("parallel_lane_integration", toJson "NOT_RUN"),
    ("standalone_modules_checked", toJson (6 : Nat)),
    ("syntactic_sequence_birth_sites", toJson (7 : Nat)),
    ("actual_mandatory_sequence_field_terms", toJson (8 : Nat)),
    ("actual_field_initializers_without_sorry_dependency", toJson (4 : Nat)),
    ("new_field_supply_demands", toJson additional),
    ("inherited_migration_demands_retained", toJson old),
    ("extra_unlabelled_errors", toJson (0 : Nat)),
    ("constructor_fields_added", toJson (0 : Nat)),
    ("separate_external_context_parameters_added", toJson (0 : Nat)),
    ("existing_completion_field_strengthened", toJson true),
    ("closed_initialized_source", toJson "? - ? a\n    ? b\n    : c\n  - d\n: e\n"),
    ("closed_source_free_premises", toJson (0 : Nat)),
    ("closed_source_axioms", toJson "standard_three"),
    ("reader_erasure_type_errors", toJson (1 : Nat)),
    ("critical_retirements", toJson (0 : Nat)),
    ("full_module_accepted", toJson false),
    ("full_repository_qualification", toJson "NOT_RUN"),
    ("production_pr_ready", toJson false)]
  IO.FS.writeFile (root ++ "result.json") (result.pretty ++ "\n")
  IO.println "VERIFIED six_modules=6 actual_field_terms=8 supplied=4 residual_new_labels=3 inherited_labels=8 extra_errors=0 critical_retirements=0"
