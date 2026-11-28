import Lean

open Lean

namespace R2CloseVerify

def readEvidence (path : String) : IO String := do
  if ← System.FilePath.pathExists path then return ← IO.FS.readFile path
  let result ← IO.Process.output {cmd := "xz", args := #["-dc", path ++ ".xz"]}
  unless result.exitCode == 0 do throw (IO.userError s!"missing {path}")
  return result.stdout

def errors (log : String) : Array String :=
  log.splitOn "\n" |>.filterMap (fun line =>
    if line.contains ": error" then some ((line.splitOn ": error: ").getLast!) else none) |>.toArray

def checkErrors (path : String) (expected : Array String) : IO String := do
  let log ← readEvidence path
  let actual := errors log
  unless actual.size == expected.size && actual.all expected.contains && expected.all actual.contains do
    throw (IO.userError s!"{path}: expected {expected}; actual {actual}")
  IO.println s!"EXACT-DIAGNOSTIC {path}: demands={actual.size} extra=0"
  return log

def profile (log declaration : String) : IO String := do
  let parts := log.splitOn ("'" ++ declaration ++ "' depends on axioms: [")
  unless parts.length == 2 do throw (IO.userError s!"profile absent or ambiguous: {declaration}")
  return ((parts[1]!).splitOn "]").head!

def residual : Array String := #[
  "R2_NODE_KEYLESS_COLON_ANCESTORS", "R2_NODE_QUESTION_ANCESTORS",
  "R2_NODE_IMPLICIT_COLON_NO_TAIL", "R2_NODE_IMPLICIT_COLON_ANCESTORS",
  "R2_NODE_PROPS_COLON_NO_TAIL", "R2_NODE_PROPS_COLON_ANCESTORS",
  "R2_SEQUENCE_LANDED_LEFT_OF_SLOT", "R2_SEQUENCE_LANDED_MISSING_SLOT"]

def main : IO Unit := do
  let parent ← readEvidence "Research/R2UnmarkedOwner/logs/integrated-diagnostic.log"
  let before := errors parent
  unless before.size == 20 && residual.all before.contains do
    throw (IO.userError "frozen integrated comparison is not the declared 20-demand parent")
  let log ← checkErrors "Research/R2CloseValueFamily/logs/final-audited.log" residual
  let removed := before.filter (!residual.contains ·)
  unless removed.size == 12 && removed.contains "R2_COLON_CLOSE_WHOLE_VALUE" do
    throw (IO.userError "third-caller boundary absent from exact removed roster")
  for marker in [
    "WHOLE-VALUE-AUDIT content_and_properties=14 flow_writers=3 field_sorry_terms=0 flow_opener_sorryAx=absent actual_close_readers=2",
    "UNMARKED-OWNER-FIELDS checked=12 sorry_terms=0 actual_pair_readers=2 new_external_pair=0",
    "ACTUAL-COMPLETION-FIELDS ordinary=3 decorated=3 checked=6 helper_terms=6 sorry_terms=0",
    "COMPOSITION-AUDIT colon_helpers=2/2 axioms=5 sorryAx=absent actual_landed_reader=present",
    "STORED-CONTEXT-AUDIT fields=#[h_expl, h_kslot, h_explUp]"] do
    unless log.contains marker do throw (IO.userError s!"missing actual-source audit: {marker}")
  for declaration in ["L4YAML.Proofs.StreamAccum.colon_open_map_explicit",
      "L4YAML.Proofs.StreamAccum.compact_open_map",
      "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented"] do
    unless (← profile parent declaration) == (← profile log declaration) do
      throw (IO.userError s!"printed producer axiom profile changed: {declaration}")
    IO.println s!"PRODUCER-AXIOMS {declaration}: printed_byte_identical=true"
  let flow ← profile log "L4YAML.Proofs.StreamAccum.accum_flow_open_depth0"
  unless flow == "propext, Classical.choice, Quot.sound" do
    throw (IO.userError s!"unexpected whole flow-opener axioms: {flow}")
  let ablated ← readEvidence "Research/R2CloseValueFamily/logs/erased-reader.log"
  let erasureErrors := errors ablated
  let extra := erasureErrors.filter (!residual.contains ·)
  unless erasureErrors.size == 9 && residual.all erasureErrors.contains &&
      extra.size == 1 && extra[0]!.toLower.contains "type mismatch" do
    throw (IO.userError s!"unexpected actual reader-erasure result: {erasureErrors}")
  IO.println "ACTUAL-COLON-READER-ERASURE retained=8 extra_type_mismatch=1"
  let proof ← readEvidence "Research/R2CloseValueFamily/logs/standalone/Research-R2CloseValueFamily-DependencyAudit.log"
  unless proof.contains "required=7 forbidden=6 missing=0 free_premises=0" do
    throw (IO.userError "initialized non-nil sibling dependency audit missing")
  let replay ← readEvidence "Research/R2CloseValueFamily/logs/standalone-replay.log"
  let modules := replay.splitOn "\n" |>.filter (·.startsWith "CHECKED ")
  unless modules.length == 8 do throw (IO.userError "expected four new and four reused modules")
  let prefixLog ← readEvidence "Research/R2CloseValueFamily/logs/flow-prefix.log"
  unless (errors prefixLog).isEmpty && prefixLog.contains
      "ACCEPTED-PREFIX strong_fields=4 actual_flow_opener=checked axioms=3 sorryAx=absent later_failed_declarations=excluded" &&
      (← IO.FS.readFile "Research/R2CloseValueFamily/logs/flow-prefix.exit").trimAscii.toString == "0" do
    throw (IO.userError "isolated actual invariant and flow prefix did not accept")
  IO.println "ACTUAL-FLOW-PREFIX accepted=true strong_fields=4 whole_opener_axioms=3 global_migration=false"
  for name in ["initial-price", "funded-draft", "funded-audited", "final-audited", "erased-reader"] do
    unless (← IO.FS.readFile s!"Research/R2CloseValueFamily/logs/{name}.exit").trimAscii.toString == "1" do
      throw (IO.userError s!"rejected diagnostic exit absent: {name}")
  IO.FS.writeFile "Research/R2CloseValueFamily/result.json" (Json.pretty (Json.mkObj [
    ("state", toJson "WARRANTED_BOUNDED; UNKNOWN_FULL_MIGRATION"),
    ("parent_demands", toJson before), ("removed_demands", toJson removed),
    ("residual_demands", toJson residual),
    ("content_and_properties_field_terms", toJson (14 : Nat)),
    ("flow_informative_writers", toJson (3 : Nat)),
    ("new_standalone_modules_checked", toJson (4 : Nat)),
    ("reused_modules_rechecked", toJson (4 : Nat)),
    ("actual_flow_prefix_accepted", toJson true),
    ("full_module_accepted", toJson false),
    ("critical_retirements", toJson (0 : Nat)),
    ("normalized_route_domains", toJson true),
    ("changed_contract_counts_are_debt_scores", toJson false)]))
  IO.println "WARRANT third_colon_supplier=funded retained_demands=8 extra_errors=0 new_field_terms=17 full_module=false critical_retirements=0"

end R2CloseVerify

def main (_args : List String) := R2CloseVerify.main
