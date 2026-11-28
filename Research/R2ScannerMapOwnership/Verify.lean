import Lean
open Lean

namespace R2MapVerify

def readEvidence (path : String) : IO String := do
  if ← System.FilePath.pathExists path then return ← IO.FS.readFile path
  let result ← IO.Process.output {cmd := "bash", args := #["-o", "pipefail", "-c",
    "base64 --decode \"$1\" | xz -dc", "map-evidence", path ++ ".xz.b64"]}
  unless result.exitCode == 0 do throw (IO.userError s!"missing {path}")
  return result.stdout

def remaining : Array String := #[
  "R2_NODE_KEYLESS_COLON_ANCESTORS", "R2_NODE_QUESTION_ANCESTORS",
  "R2_NODE_IMPLICIT_COLON_NO_TAIL", "R2_NODE_IMPLICIT_COLON_ANCESTORS",
  "R2_NODE_PROPS_COLON_NO_TAIL", "R2_NODE_PROPS_COLON_ANCESTORS",
  "R2_SEQUENCE_LANDED_LEFT_OF_SLOT", "R2_SEQUENCE_LANDED_MISSING_SLOT"]

def main : IO Unit := do
  for phase in ["map-thread-second", "map-thread-audited"] do
    let path := s!"Research/R2ScannerMapOwnership/logs/{phase}"
    unless (← IO.FS.readFile (path ++ ".exit")).trimAscii.toString == "1" do
      throw (IO.userError s!"wrong full diagnostic exit: {path}")
    let log ← readEvidence (path ++ ".log")
    let actual := log.splitOn "\n" |>.filterMap (fun line =>
      if line.contains ": error" then some ((line.splitOn ": error: ").getLast!) else none) |>.toArray
    unless actual.size == 8 && actual.all remaining.contains && remaining.all actual.contains do
      throw (IO.userError s!"wrong full diagnostic: {actual}")
    if phase == "map-thread-audited" then
      for marker in [
          "MAP-THREAD-AUDIT actual_seed=present actual_recursive_step=present public_external_maps_premise=absent step_axioms=standard_three",
          "ACTUAL-COMPLETION-FIELDS ordinary=3 decorated=3 checked=6 helper_terms=6 sorry_terms=0",
          "UNMARKED-OWNER-FIELDS checked=12 sorry_terms=0 actual_pair_readers=2 new_external_pair=0",
          "CLOSE-FAMILY-AUDIT field_writers=31 actual_colon_calls=2 sorry_terms=0 local_definitions=substituted"] do
        unless log.contains marker do throw (IO.userError s!"audit missing {marker}")
    IO.println s!"EXACT-DIAGNOSTIC {phase} errors=8 extra=0 full_accepted=false"
  let audit ← readEvidence "Research/R2ScannerMapOwnership/logs/Audit.log"
  unless audit.contains "MAP-OWNERSHIP-AXIOMS step=standard_three separation=standard_three initialized=standard_three_plus_four_inherited_native_leaves custom=0 sorryAx=0" do
    throw (IO.userError "checked axiom audit missing")
  let replay ← readEvidence "Research/R2ScannerMapOwnership/logs/standalone-replay.log"
  let checked := replay.splitOn "\n" |>.filter (·.startsWith "CHECKED ")
  unless checked.length == 12 do throw (IO.userError s!"replay inventory changed: {checked}")
  IO.FS.writeFile "Research/R2ScannerMapOwnership/result.json" (Json.pretty (Json.mkObj [
    ("state", toJson "WARRANTED_SCANNER_OWNERSHIP; UNKNOWN_SEMANTIC_MIGRATION"),
    ("arbitrary_inputs_and_prefix_lengths", toJson true),
    ("actual_recursive_step_and_root_connected", toJson true),
    ("new_public_ownership_premise", toJson false),
    ("old_sound_implies_maps", toJson false),
    ("remaining_demands", toJson remaining), ("extra_errors", toJson (0 : Nat)),
    ("full_module_accepted", toJson false), ("critical_retirements", toJson (0 : Nat)),
    ("own_modules_checked", toJson (8 : Nat)), ("snapshot_dependencies_checked", toJson (4 : Nat)),
    ("new_step_axioms", toJson (0 : Nat)), ("initialized_inherited_native_leaves", toJson (4 : Nat))]))
  IO.println "WARRANT initialized_prefix_ownership=true actual_loop_threaded=true errors=8 full_module=false critical_retirements=0"

end R2MapVerify
def main := R2MapVerify.main
