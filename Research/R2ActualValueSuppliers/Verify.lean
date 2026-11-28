import Lean

open Lean

def decodedLog (root name : String) : IO String := do
  let result ← IO.Process.output {
    cmd := "bash"
    args := #["-o", "pipefail", "-c", "base64 --decode \"$1\" | xz --decompress --stdout",
      "r2-value-log", root ++ "/logs/" ++ name ++ ".log.xz.b64"] }
  unless result.exitCode == 0 do throw (IO.userError s!"cannot decode {name}: {result.stderr}")
  pure result.stdout

def main : IO Unit := do
  let root := "Research/R2ActualValueSuppliers"
  let hashes ← IO.Process.output {cmd := "sha256sum", args := #["--check", "EVIDENCE.sha256"], cwd := root}
  unless hashes.exitCode == 0 do throw (IO.userError ("evidence hash failure: " ++ hashes.stdout ++ hashes.stderr))
  let modules := #["Controls", "Producers", "First", "Unkeyed", "Witness", "Audit"]
  for name in modules do
    unless (← IO.FS.readFile (root ++ "/logs/" ++ name ++ ".exit")).trimAscii.toString == "0" do
      throw (IO.userError s!"rejected proof module {name}")
    let log ← decodedLog root name
    if log.contains ": error:" then throw (IO.userError s!"compiler error retained in accepted {name}")
    if log.contains "sorryAx" then throw (IO.userError s!"sorry dependency retained in accepted {name}")
  let audit ← decodedLog root "Audit"
  let boundary := "ACTUAL-VALUE-AUDIT required=12 forbidden=9 dependencies=7855 free_premises=0 pure_roots=14 axioms=standard_three"
  unless audit.contains boundary do throw (IO.userError "dependency audit boundary changed")
  let witness ← decodedLog root "Witness"
  unless witness.contains "[propext, Classical.choice, Quot.sound]" do
    throw (IO.userError "initialized source axiom boundary missing")
  unless (← IO.FS.readFile (root ++ "/logs/ErasedReader.exit")).trimAscii.toString == "1" do
    throw (IO.userError "erased reader was not rejected")
  let erased ← decodedLog root "ErasedReader"
  unless (erased.splitOn ": error:").length == 2 && erased.contains "Application type mismatch" &&
      erased.contains "actual_same_implicit" && erased.contains "Context (dispatchState p6)" do
    throw (IO.userError "erasure no longer fails once at the actual reader")
  let result := Json.mkObj [
    ("state", toJson "WARRANTED_LOCAL_ACTUAL_COLON_SUPPLIERS; UNKNOWN_FULL_MIGRATION"),
    ("parent", toJson "b26c9bfd3e07b54f5b9bf74a7f3f4397e543cf7a"),
    ("proof_modules_checked", toJson modules.size),
    ("named_first_and_same_saved_key_variants", toJson (6 : Nat)),
    ("additional_cleared_keyless_variant", toJson true),
    ("generic_and_closed_roots_standard_three", toJson (14 : Nat)),
    ("initialized_source", toJson "? - a: b\n    c: d\n  - e\n: f\n"),
    ("initialized_source_free_premises", toJson (0 : Nat)),
    ("dependency_closure", toJson (7855 : Nat)),
    ("required_dependencies", toJson (12 : Nat)),
    ("forbidden_dependencies", toJson (9 : Nat)),
    ("erased_reader_type_errors", toJson (1 : Nat)),
    ("constructor_fields_added", toJson (0 : Nat)),
    ("production_files_changed", toJson (0 : Nat)),
    ("full_migration", toJson "UNKNOWN"),
    ("global_constructor_inventory_remeasured", toJson false),
    ("critical_retirements", toJson (0 : Nat)),
    ("last_accepted_critical_count", toJson (7 : Nat)),
    ("retirement_lane_integration", toJson "NOT_RUN"),
    ("full_repository_qualification", toJson "NOT_RUN"),
    ("production_pr_ready", toJson false),
    ("ledger_replay_is_fresh_kernel_build", toJson false)]
  IO.FS.writeFile (root ++ "/result.json") (result.pretty ++ "\n")
  IO.println "ACTUAL-VALUE-LEDGER accepted_modules=6 pure_roots=14 initialized_free_premises=0 reader_errors=1 full_migration=UNKNOWN critical_retirements=0"
