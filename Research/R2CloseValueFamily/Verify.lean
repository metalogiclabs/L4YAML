import Lean

open Lean
namespace R2CloseVerify

def readEvidence (path : String) : IO String := do
  if ← System.FilePath.pathExists path then return ← IO.FS.readFile path
  let archive := path ++ ".xz"
  let result ← if ← System.FilePath.pathExists archive then
      IO.Process.output {cmd := "xz", args := #["-dc", archive]}
    else
      IO.Process.output {cmd := "bash", args := #["-o", "pipefail", "-c",
        "base64 --decode \"$1\" | xz -dc", "close-evidence", archive ++ ".b64"]}
  unless result.exitCode == 0 do throw (IO.userError s!"missing {path}")
  return result.stdout

def errors (log : String) : Array String :=
  log.splitOn "\n" |>.filterMap (fun line =>
    if line.contains ": error" then some ((line.splitOn ": error: ").getLast!) else none) |>.toArray

def remaining : Array String := #[
  "R2_NODE_KEYLESS_COLON_ANCESTORS", "R2_NODE_QUESTION_ANCESTORS",
  "R2_NODE_IMPLICIT_COLON_NO_TAIL", "R2_NODE_IMPLICIT_COLON_ANCESTORS",
  "R2_NODE_PROPS_COLON_NO_TAIL", "R2_NODE_PROPS_COLON_ANCESTORS",
  "R2_SEQUENCE_LANDED_LEFT_OF_SLOT", "R2_SEQUENCE_LANDED_MISSING_SLOT"]

def funded : Array String := #[
  "R2_RETAIN_FLOW_SEQUENCE_CLOSE_PAIR", "R2_RETAIN_FLOW_MAPPING_CLOSE_PAIR",
  "R2_COLON_CLOSE_WHOLE_VALUE", "R2_RETAIN_PROPS_EMPTY_COLON_PAIR",
  "R2_RETAIN_PROPS_EMPTY_INDICATOR_PAIR", "R2_RETAIN_PENDING_VALUE_EMPTY_PAIR",
  "R2_RETAIN_PENDING_ENTRY_UNION_PAIR", "R2_RETAIN_PROPS_KEY_1_PAIR",
  "R2_RETAIN_PROPS_KEY_2_PAIR", "R2_RETAIN_PROPS_KEY_3_PAIR",
  "R2_RETAIN_PROPS_KEY_4_PAIR", "R2_RETAIN_PROPS_KEY_5_PAIR"]

def sameErrors (path : String) (expected : Array String) : IO String := do
  let log ← readEvidence path
  let actual := errors log
  unless actual.size == expected.size && actual.all expected.contains && expected.all actual.contains do
    throw (IO.userError s!"{path}: expected {expected}, actual {actual}")
  IO.println s!"EXACT-DIAGNOSTIC {path} demands={actual.size} extra=0"
  return log

def profile (log declaration : String) : IO String := do
  let parts := log.splitOn ("'" ++ declaration ++ "' depends on axioms: [")
  unless parts.length == 2 do throw (IO.userError s!"profile absent or ambiguous: {declaration}")
  return ((parts[1]!).splitOn "]").head!

def raw (log marker : String) : IO String := do
  let parts := log.splitOn marker
  unless parts.length == 2 do throw (IO.userError s!"raw marker absent or ambiguous: {marker}")
  return ((parts[1]!).splitOn "]").head! ++ "]"

def main : IO Unit := do
  let parent ← sameErrors "Research/R2UnmarkedOwner/logs/integrated-diagnostic.log" (remaining ++ funded)
  let positive ← sameErrors "Research/R2CloseValueFamily/logs/repaired-v1.log" remaining
  let audit ← sameErrors "Research/R2CloseValueFamily/logs/audited-final.log" remaining
  for marker in [
      "ACTUAL-COMPLETION-FIELDS ordinary=3 decorated=3 checked=6 helper_terms=6 sorry_terms=0",
      "UNMARKED-OWNER-FIELDS checked=12 sorry_terms=0 actual_pair_readers=2 new_external_pair=0",
      "COMPOSITION-AUDIT colon_helpers=2/2 axioms=5 sorryAx=absent actual_landed_reader=present",
      "CLOSE-FIELD-TOTAL h_vpack writers=12 sorry_terms=0",
      "CLOSE-FIELD-TOTAL h_kslot writers=6 sorry_terms=0",
      "CLOSE-FIELD-TOTAL vslot writers=13 sorry_terms=0",
      "CLOSE-FAMILY-AUDIT field_writers=31 actual_colon_calls=2 sorry_terms=0 local_definitions=substituted"] do
    unless audit.contains marker do throw (IO.userError s!"actual audit missing {marker}")
  for producer in ["accum_flow_open_depth0", "accum_step_flow"] do
    let marker := "CLOSE-PRODUCER-AXIOMS L4YAML.Proofs.StreamAccum." ++ producer ++
      " #[`propext, `Classical.choice, `Quot.sound]"
    unless audit.contains marker do throw (IO.userError s!"standard-only flow profile missing {producer}")
  for declaration in ["L4YAML.Proofs.StreamAccum.colon_open_map_explicit",
      "L4YAML.Proofs.StreamAccum.compact_open_map",
      "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented"] do
    let before ← profile parent declaration
    unless (← profile positive declaration) == before && (← profile audit declaration) == before do
      throw (IO.userError s!"inherited axiom profile changed {declaration}")
    IO.println s!"INHERITED-AXIOMS {declaration} byte_identical=true"
  let completionMarker := "RAW-SEQUENCE-COMPLETION-AXIOMS "
  unless (← raw parent completionMarker) == (← raw audit completionMarker) do
    throw (IO.userError "inherited completion raw axiom profile changed")
  let erased ← readEvidence "Research/R2CloseValueFamily/logs/erased-reader.log"
  let actual := errors erased
  let extra := actual.filter (!remaining.contains ·)
  unless actual.size == 9 && extra.size == 1 && remaining.all actual.contains &&
      extra[0]!.toLower.contains "type mismatch" do
    throw (IO.userError s!"unexpected actual-reader erasure {actual}")
  let proof ← readEvidence "Research/R2CloseValueFamily/logs/DependencyAudit.log"
  unless proof.contains "required=9 forbidden=4 missing=0 free_premises=0" do
    throw (IO.userError "initialized proof dependency audit absent")
  let replay ← readEvidence "Research/R2CloseValueFamily/logs/standalone-replay.log"
  let modules := replay.splitOn "\n" |>.filter (·.startsWith "CHECKED ")
  unless modules.length == 4 do throw (IO.userError "standalone replay must check four modules")
  IO.FS.writeFile "Research/R2CloseValueFamily/result.json" (Json.pretty (Json.mkObj [
    ("state", toJson "WARRANTED_BOUNDED; UNKNOWN_FULL_MIGRATION"),
    ("parent_demands", toJson (20 : Nat)), ("funded_demands", toJson funded),
    ("remaining_demands", toJson remaining), ("extra_errors", toJson (0 : Nat)),
    ("erasure_extra_type_errors", toJson (1 : Nat)),
    ("new_standalone_modules_checked", toJson modules.length),
    ("critical_retirements", toJson (0 : Nat)), ("full_module_accepted", toJson false),
    ("changed_contract_counts_are_debt_scores", toJson false)]))
  IO.println "WARRANT parent=20 remaining=8 funded_labels=12 replacement_labels=0 reader_erasure_extra=1 full_module=false critical_retirements=0"

end R2CloseVerify

def main := R2CloseVerify.main
