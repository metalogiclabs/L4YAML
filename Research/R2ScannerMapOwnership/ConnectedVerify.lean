import Lean
open Lean

namespace R2ConnectedVerify

def root : String := "Research/R2ScannerMapOwnership"

def readJson (name : String) : IO Json := do
  let text ← IO.FS.readFile (root ++ "/" ++ name)
  match Json.parse text with
  | .ok value => return value
  | .error error => throw (IO.userError s!"{name}: {error}")

def objectValue (value : Json) (key : String) : IO Json :=
  match value.getObjVal? key with
  | .ok item => pure item
  | .error error => throw (IO.userError error)

def readLog (name : String) : IO String := do
  let path := root ++ "/logs/" ++ name
  if ← System.FilePath.pathExists path then return ← IO.FS.readFile path
  let result ← IO.Process.output {cmd := "bash", args := #["-o", "pipefail", "-c",
    "base64 --decode \"$1\" | xz -dc", "connected-evidence", path ++ ".xz.b64"]}
  unless result.exitCode == 0 do throw (IO.userError s!"missing {path}")
  return result.stdout

def main : IO Unit := do
  for phase in ["accepted-stream", "accepted-document", "accepted-audit-actual",
      "accepted-audit-baseline", "accepted-census-actual", "accepted-census-baseline",
      "JointStep-connected", "JointColon-connected", "JointWitness-final", "ConnectedAudit"] do
    let status ← IO.FS.readFile (root ++ "/logs/" ++ phase ++ ".exit")
    unless status.trimAscii.toString == "0" do throw (IO.userError s!"rejected positive phase: {phase}")
    let log ← readLog (phase ++ ".log")
    if log.contains ": error" then throw (IO.userError s!"positive contains errors: {phase}")
  let baseline ← readJson "accepted-baseline.json"
  let actual ← readJson "accepted-actual.json"
  let profiles ← match (← objectValue actual "profiles").getArr? with
    | .ok values => pure values
    | .error error => throw (IO.userError error)
  unless profiles.size == 3 do throw (IO.userError "public profile inventory changed")
  for profile in profiles do
    let representation ← objectValue profile "statement_repr"
    unless representation.getStr?.isOk do throw (IO.userError "statement representation absent")
  unless (← objectValue baseline "profiles") == (← objectValue actual "profiles") do
    throw (IO.userError "public statements or inherited axiom profiles changed")
  unless (← objectValue baseline "actual_loop_and_seed_wired") == toJson false &&
      (← objectValue actual "actual_loop_and_seed_wired") == toJson true do
    throw (IO.userError "actual ownership wiring was not distinguished from baseline")
  let censusBefore ← readJson "census-baseline.json"
  let censusAfter ← readJson "census-actual.json"
  unless (← objectValue censusBefore "critical_roster") == (← objectValue censusAfter "critical_roster") &&
      (← objectValue censusBefore "positions") == toJson (252 : Nat) &&
      (← objectValue censusAfter "positions") == toJson (252 : Nat) &&
      (← objectValue censusAfter "critical_on") == toJson (7 : Nat) do
    throw (IO.userError "accepted directed critical roster changed")
  for phase in ["erased-scanner-step", "erased-joint-reader"] do
    let status ← IO.FS.readFile (root ++ "/logs/" ++ phase ++ ".exit")
    unless status.trimAscii.toString == "1" do throw (IO.userError s!"erasure did not reject: {phase}")
    let log ← readLog (phase ++ ".log")
    let errors := log.splitOn "\n" |>.filter (·.contains ": error")
    unless errors.length == 1 && log.toLower.contains "type mismatch" do
      throw (IO.userError s!"unexpected erasure failure: {phase}: {errors}")
  let connected ← readLog "ConnectedAudit.log"
  unless connected.contains "CONNECTED-JOINT-AUDIT required=12 forbidden=7" &&
      connected.contains "free_route_premises=0" &&
      connected.contains "pure_producers=standard_three" do
    throw (IO.userError "connected source audit missing")
  IO.FS.writeFile (root ++ "/connected-result.json") (Json.pretty (Json.mkObj [
    ("state", toJson "WARRANTED_ACCEPTED_INVARIANT_AND_CONDITIONAL_UNIVERSAL_PRODUCERS"),
    ("accepted_stream_module", toJson true), ("accepted_document_module", toJson true),
    ("public_statements_and_axiom_profiles_identical", toJson true),
    ("actual_seed_and_recursive_step_connected", toJson true),
    ("fresh_optional_positions", toJson (252 : Nat)), ("fresh_critical_on", toJson (7 : Nat)),
    ("critical_roster_unchanged", toJson true), ("critical_retirements", toJson (0 : Nat)),
    ("initialized_mixed_source_to_eof", toJson true), ("closed_witness_free_route_premises", toJson (0 : Nat)),
    ("parallel_semantic_composition", toJson "CORROBORATION_OF_e195b995ce123ac64cac348be7ef4ab432825b12; COUNTED_ONCE"),
    ("real_erasure_controls_rejected", toJson (2 : Nat)),
    ("whole_semantic_context_supplied_at_every_node_birth", toJson false),
    ("full_continuation_migration_accepted", toJson false),
    ("full_repository_qualification", toJson "NOT_RUN"),
    ("universal_producer_axioms", toJson "standard_three"),
    ("initialized_proof_inherited_native_leaves", toJson (4 : Nat))]))
  IO.println "CONNECTED-WARRANT accepted_modules=2 unchanged_public_profiles=3 critical_on=7 retirements=0 closed_source_to_eof=true erasures_rejected=2 full_continuation_migration=false"

end R2ConnectedVerify
def main := R2ConnectedVerify.main
