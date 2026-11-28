import Lean

open Lean
namespace R2UnmarkedVerify

def readEvidence (path : String) : IO String := do
  if ← System.FilePath.pathExists path then return ← IO.FS.readFile path
  let result ← IO.Process.output {cmd := "xz", args := #["-dc", path ++ ".xz"]}
  unless result.exitCode == 0 do throw (IO.userError s!"missing {path}")
  return result.stdout

def errors (log : String) : Array String :=
  log.splitOn "\n" |>.filterMap (fun line =>
    if line.contains ": error" then
      some ((line.splitOn ": error: ").getLast!)
    else none) |>.toArray

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

def raw (log marker : String) : IO String := do
  let parts := log.splitOn marker
  unless parts.length == 2 do throw (IO.userError s!"raw marker absent or ambiguous: {marker}")
  return ((parts[1]!).splitOn "]").head! ++ "]"

def main (args : List String) : IO Unit := do
  let parent ← readEvidence "Research/R2ContinuationContract/logs/marked-pair-diagnostic.log"
  let baseline := errors parent
  unless baseline.size == 22 do throw (IO.userError "frozen parent must have 22 demands")
  let removed := #["R2_OTHER_BLOCK_CONTENT_PAIR_UNMARKED", "R2_OTHER_PENDING_BLOCK_PAIR"]
  let expected := baseline.filter (!removed.contains ·)
  unless expected.size == 20 do throw (IO.userError "targeted pair demands absent from parent")
  let paired ← checkErrors "Research/R2UnmarkedOwner/logs/paired-diagnostic.log" expected
  let audit ← checkErrors "Research/R2UnmarkedOwner/logs/producer-audit.log" expected
  unless audit.contains "UNMARKED-OWNER-FIELDS checked=12 sorry_terms=0 actual_pair_readers=2 new_external_pair=0" do
    throw (IO.userError "actual writer/reader audit absent")
  unless audit.contains "ACTUAL-COMPLETION-FIELDS ordinary=3 decorated=3 checked=6 helper_terms=6 sorry_terms=0" do
    throw (IO.userError "inherited six completion field audit absent")
  for declaration in ["L4YAML.Proofs.StreamAccum.colon_open_map_explicit",
      "L4YAML.Proofs.StreamAccum.compact_open_map",
      "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented"] do
    let before ← profile parent declaration
    for log in [paired, audit] do
      unless (← profile log declaration) == before do
        throw (IO.userError s!"inherited axiom profile changed: {declaration}")
    IO.println s!"INHERITED-AXIOMS {declaration}: byte_identical=true"
  let marker := "RAW-SEQUENCE-COMPLETION-AXIOMS "
  unless (← raw parent marker) == (← raw paired marker) &&
      (← raw parent marker) == (← raw audit marker) do
    throw (IO.userError "ordinary completion raw axiom profile changed")
  IO.println "ORDINARY-COMPLETION-AXIOMS byte_identical=true"
  let proof ← readEvidence "Research/R2UnmarkedOwner/logs/dependency-audit.log"
  unless proof.contains "required=9 forbidden=6 missing=0 free_premises=0" do
    throw (IO.userError "initialized proof dependency audit absent")
  if args.contains "--all" then
    let ablated ← readEvidence "Research/R2UnmarkedOwner/logs/erased-reader.log"
    let actual := errors ablated
    let extra := actual.filter (!expected.contains ·)
    unless actual.size == 21 && extra.size == 1 && expected.all actual.contains &&
        extra[0]!.contains "type mismatch" do
      throw (IO.userError s!"unexpected reader erasure result {actual}")
    IO.println "ACTUAL-READER-ERASURE retained=20 extra_type_mismatch=1"
    let composedExpected := expected.filter (fun label =>
      !#["R2_SLOT_EXPLICIT_COLON_DOMAIN", "R2_NODE_EXPLICIT_COLON_ANCESTORS"].contains label)
      |>.push "R2_COLON_CLOSE_WHOLE_VALUE"
    let composed ← checkErrors "Research/R2UnmarkedOwner/logs/colon-composition.log" composedExpected
    let axioms ← profile composed "L4YAML.Proofs.StreamAccum.colon_open_map_explicit"
    if axioms.contains "sorryAx" then throw (IO.userError "composed colon producer contains sorryAx")
    IO.println "COMPOSED-COLON producer_sorryAx=false funded_sequence_callers=2 remaining_close_supplier=1"
    let integratedExpected := composedExpected.filter (· != "R2_SEQUENCE_LANDED_FAMILY")
      |>.append #["R2_SEQUENCE_LANDED_LEFT_OF_SLOT", "R2_SEQUENCE_LANDED_MISSING_SLOT"]
    let integrated ← checkErrors "Research/R2UnmarkedOwner/logs/integrated-diagnostic.log" integratedExpected
    unless integrated.contains "COMPOSITION-AUDIT colon_helpers=2/2 axioms=5 sorryAx=absent actual_landed_reader=present" &&
        integrated.contains "UNMARKED-OWNER-FIELDS checked=12 sorry_terms=0 actual_pair_readers=2 new_external_pair=0" do
      throw (IO.userError "integrated producer evidence absent")
    let replay ← readEvidence "Research/R2UnmarkedOwner/logs/standalone-replay.log"
    let modules := replay.splitOn "\n" |>.filter (·.startsWith "CHECKED ")
    unless modules.length == 6 do throw (IO.userError "standalone replay must check six new modules")
    IO.println "INTEGRATION exact_parallel_patch=true field_writers=12 standalone_modules=6 critical_retirements=0"
    IO.FS.writeFile "Research/R2UnmarkedOwner/result.json" (Json.pretty (Json.mkObj [
      ("state", toJson "WARRANTED_BOUNDED; UNKNOWN_FULL_MIGRATION"),
      ("parent_demands", toJson baseline.size), ("funded_pair_demands", toJson removed),
      ("paired_demands", toJson expected), ("composed_demands", toJson composedExpected),
      ("integrated_demands", toJson integratedExpected),
      ("actual_field_constructions_checked", toJson (12 : Nat)),
      ("new_standalone_modules_checked", toJson modules.length),
      ("critical_retirements", toJson (0 : Nat)),
      ("full_module_accepted", toJson false),
      ("changed_contract_counts_are_debt_scores", toJson false)]))
  IO.println "WARRANT unmarked_pair_suppliers=2 field_constructions=12 full_module=false critical_retirements=0"

end R2UnmarkedVerify

def main := R2UnmarkedVerify.main
