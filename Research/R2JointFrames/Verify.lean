import Lean

open Lean
namespace R2JointVerify

def readEvidence (path : String) : IO String := do
  if ← System.FilePath.pathExists path then return ← IO.FS.readFile path
  let result ← IO.Process.output {cmd := "xz", args := #["-dc",path++".xz"]}
  unless result.exitCode == 0 do throw (IO.userError s!"missing {path}")
  return result.stdout

def errors (log : String) : Array String :=
  log.splitOn "\n" |>.filterMap (fun line =>
    if line.contains ": error" then some ((line.splitOn ": error: ").getLast!) else none) |>.toArray

def profile (log declaration : String) : IO String := do
  let parts := log.splitOn ("'"++declaration++"' depends on axioms: [")
  unless parts.length == 2 do throw (IO.userError s!"profile missing or ambiguous {declaration}")
  return ((parts[1]!).splitOn "]").head!

def main : IO Unit := do
  let parent ← readEvidence "Research/R2CloseValueFamily/logs/final-audited.log"
  let baseline := errors parent
  unless baseline.size == 8 do throw (IO.userError "frozen parent does not have eight demands")
  for path in ["Research/R2JointFrames/logs/total-block.log",
      "Research/R2JointFrames/logs/total-audited.log",
      "Research/R2JointFrames/logs/removed-audited.log"] do
    let log ← readEvidence path
    let actual := errors log
    unless actual.size == 8 && actual.all baseline.contains && baseline.all actual.contains do
      throw (IO.userError s!"diagnostic changed {path}: {actual}")
    IO.println s!"EXACT-DIAGNOSTIC {path}: retained=8 extra=0"
  let audited ← readEvidence "Research/R2JointFrames/logs/total-audited.log"
  let removed ← readEvidence "Research/R2JointFrames/logs/removed-audited.log"
  unless removed.contains "REMOVED-PACK-AUDIT constructor_field=absent actual_writers=7 actual_readers=3 projection_axioms=3 full_migration=unknown" do
    throw (IO.userError "actual field-deletion audit missing")
  for marker in [
      "TOTAL-PACK-AUDIT constructor_field=required actual_writers=7 projection_axioms=3 new_external_family=absent full_migration=unknown",
      "UNMARKED-OWNER-FIELDS checked=12 sorry_terms=0 actual_pair_readers=2 new_external_pair=0",
      "ACTUAL-COMPLETION-FIELDS ordinary=3 decorated=3 checked=6 helper_terms=6 sorry_terms=0",
      "WHOLE-VALUE-AUDIT content_and_properties=14 flow_writers=3 field_sorry_terms=0 flow_opener_sorryAx=absent actual_close_readers=2"] do
    unless audited.contains marker do throw (IO.userError s!"missing actual-source audit {marker}")
  for declaration in ["L4YAML.Proofs.StreamAccum.colon_open_map_explicit",
      "L4YAML.Proofs.StreamAccum.compact_open_map",
      "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented"] do
    unless (← profile parent declaration) == (← profile audited declaration) &&
        (← profile parent declaration) == (← profile removed declaration) do
      throw (IO.userError s!"printed producer profile changed {declaration}")
  let prefixLog ← readEvidence "Research/R2JointFrames/logs/total-prefix.log"
  unless (errors prefixLog).isEmpty && prefixLog.contains
      "TOTAL-PACK-PREFIX constructor_field=required actual_flow_opener=checked axioms=3 later_eight_demands=excluded" do
    throw (IO.userError "accepted prefix evidence missing")
  unless (← IO.FS.readFile "Research/R2JointFrames/logs/total-prefix.exit").trimAscii.toString == "0" do
    throw (IO.userError "prefix did not accept")
  let removedPrefix ← readEvidence "Research/R2JointFrames/logs/removed-prefix.log"
  unless (errors removedPrefix).isEmpty && removedPrefix.contains
      "REMOVED-PACK-PREFIX constructor_field=absent actual_flow_opener=checked axioms=3 later_eight_demands=excluded" &&
      (← IO.FS.readFile "Research/R2JointFrames/logs/removed-prefix.exit").trimAscii.toString == "0" do
    throw (IO.userError "field-deletion prefix did not accept")
  let replay ← readEvidence "Research/R2JointFrames/logs/standalone-replay.log"
  let modules := replay.splitOn "\n" |>.filter (·.startsWith "CHECKED ")
  unless modules.length == 10 do throw (IO.userError s!"standalone module inventory {modules.length}")
  let dependency ← readEvidence "Research/R2JointFrames/logs/dependencyaudit.log"
  let roots := dependency.splitOn "\n" |>.filter (·.startsWith "JOINT-INITIALIZED-AUDIT ")
  unless roots.length == 4 && roots.all (·.contains "required=8 forbidden=6 missing=0 free_premises=0") do
    throw (IO.userError "four initialized proof audits missing")
  unless dependency.contains "uniform_flat_reconstruction=refuted generic_P_only=true" do
    throw (IO.userError "generic separation boundary missing")
  let probe ← IO.ofExcept (Json.parse (← readEvidence "Research/R2JointFrames/landing-probe.json"))
  let rows ← IO.ofExcept probe.getArr?
  let mut accepts := 0
  let mut refuses := 0
  for row in rows do
    let scan ← IO.ofExcept (row.getObjValAs? Bool "scanner_accepts")
    let parse ← IO.ofExcept (row.getObjValAs? Bool "parser_accepts")
    unless scan == parse do throw (IO.userError "scanner/parser probe disagreement")
    if scan then accepts := accepts+1 else refuses := refuses+1
  unless rows.size == 8 && accepts == 3 && refuses == 5 do
    throw (IO.userError "landing probe boundary changed")
  IO.FS.writeFile "Research/R2JointFrames/result.json" (Json.pretty (Json.mkObj [
    ("state", toJson "WARRANTED_LOCAL_ALGEBRA_AND_INITIALIZED_CASES; CANDIDATE_TOTAL_FIELD; UNKNOWN_GLOBAL_MIGRATION"),
    ("initialized_proof_roots",toJson (4 : Nat)),
    ("standalone_modules_checked",toJson modules.length),
    ("generic_flat_reconstruction",toJson "REJECTED_UNIFORMLY_IN_P; FIXED_STREAM_CASE_NOT_REFUTED"),
    ("total_field_actual_writers",toJson (7 : Nat)),
    ("redundant_field",toJson "ABSENT_IN_REJECTED_DIAGNOSTIC; UNKNOWN_ACCEPTED_MIGRATION"),
    ("full_diagnostic_demands",toJson baseline),
    ("full_module_accepted",toJson false),
    ("isolated_prefix_accepted",toJson true),
    ("critical_retirements",toJson (0 : Nat)),
    ("production_pr_ready",toJson false)]))
  IO.println "JOINT-RECEIPT modules=10 initialized_roots=4 actual_writers=7 derived_readers=3 field=removed retained_demands=8 extra_errors=0 prefixes=accepted full_migration=unknown critical_retirements=0 pr_ready=false"

end R2JointVerify
def main (_args : List String) := R2JointVerify.main
