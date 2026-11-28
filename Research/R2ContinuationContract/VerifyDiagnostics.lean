import Lean

open Lean

def readJson (path : System.FilePath) : IO Json := do
  let bytes ← IO.FS.readFile path
  match Json.parse bytes with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{path}: {error}")

def readEvidence (path : System.FilePath) : IO String := do
  if ← path.pathExists then return ← IO.FS.readFile path
  let result ← IO.Process.output { cmd := "xz", args := #["-dc", path.toString ++ ".xz"] }
  unless result.exitCode == 0 do throw (IO.userError s!"cannot read evidence {path}: {result.stderr}")
  return result.stdout

def errorMessages (log : String) : Array String :=
  log.splitOn "\n" |>.filterMap (fun line =>
    match line.splitOn ": error: " with
    | [_prefix, error] => some error
    | _ => none) |>.toArray

def requireMessages (path : System.FilePath) (expected : Array String) : IO String := do
  let log ← readEvidence path
  let actual := errorMessages log
  unless actual.size == expected.size && actual.all expected.contains && expected.all actual.contains do
    throw (IO.userError s!"{path}: expected {expected}, observed {actual}")
  IO.println s!"DIAGNOSTIC {path.fileName.getD "log"}: exact_errors={actual.size} extra=0"
  return log

def rawArrayAfter (text marker : String) : IO String := do
  let parts := text.splitOn marker
  unless parts.length == 2 do throw (IO.userError s!"nonunique marker: {marker}")
  let rest := parts[1]!
  let array := (rest.splitOn "]").head! ++ "]"
  unless array.startsWith "#[" do throw (IO.userError s!"missing axiom array: {marker}")
  return array

def printedAxioms (text declaration : String) : IO String := do
  let marker := "'" ++ declaration ++ "' depends on axioms: ["
  let parts := text.splitOn marker
  unless parts.length == 2 do throw (IO.userError s!"nonunique printed profile: {declaration}")
  return marker ++ ((parts[1]!).splitOn "]").head! ++ "]"

def main : IO Unit := do
  let base ← readJson "Research/R2SequenceContext/sequence-result.json"
  let .ok rows := base.getObjValAs? (Array Json) "errors"
    | throw (IO.userError "missing parent error roster")
  let mut parent := #[]
  for row in rows do
    let .ok label := row.getObjValAs? String "label"
      | throw (IO.userError "missing parent error label")
    parent := parent.push label
  unless parent.size == 23 do throw (IO.userError "wrong frozen parent roster")
  let completed := parent.filter (· != "R2_SEQUENCE_COMPLETED_FAMILY")
  unless completed.size == 22 do throw (IO.userError "completed supplier not in parent roster")
  let logs := "Research/R2ContinuationContract/logs/"
  let cold ← requireMessages (logs ++ "completion-cold-diagnostic.log") completed
  let narrowed := completed.map fun label =>
    if label == "R2_OTHER_BLOCK_CONTENT_PAIR" then
      "R2_OTHER_BLOCK_CONTENT_PAIR_UNMARKED" else label
  let paid ← requireMessages (logs ++ "marked-pair-diagnostic.log") narrowed
  let audited ← requireMessages (logs ++ "actual-field-audit.log") narrowed
  unless (audited.splitOn "ACTUAL-COMPLETION-FIELDS ordinary=3 decorated=3 checked=6 helper_terms=6 sorry_terms=0").length == 2 do
    throw (IO.userError "actual six-field proof audit absent")
  let _ ← requireMessages (logs ++ "erased-family-diagnostic.log")
    (narrowed ++ #["R2_ABLATION_ORDINARY_COMPLETION_FAMILY",
      "ordinary completion producer contains sorryAx"])
  for log in [cold, paid, audited] do
    unless (log.splitOn "COMPLETION-CONTEXT-AUDIT stored=2 readers=5/5 new_external_context=absent ordinary_sorryAx=absent").length == 2 do
      throw (IO.userError "actual producer/reader audit absent")
  let baseline ← readEvidence (logs ++ "baseline-inventory.log")
  let expected ← rawArrayAfter baseline
    "COMPLETION-BASELINE-AXIOMS L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented: "
  for log in [cold, paid, audited] do
    let actual ← rawArrayAfter log "RAW-SEQUENCE-COMPLETION-AXIOMS "
    unless actual == expected do throw (IO.userError "ordinary completion axiom profile changed")
  for declaration in ["L4YAML.Proofs.StreamAccum.colon_open_map_explicit",
      "L4YAML.Proofs.StreamAccum.compact_open_map",
      "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented"] do
    let inherited ← printedAxioms cold declaration
    for log in [paid, audited] do
      unless (← printedAxioms log declaration) == inherited do
        throw (IO.userError s!"inherited profile changed: {declaration}")
    IO.println s!"INHERITED-AXIOMS {declaration}: byte_identical=true"
  IO.FS.writeFile (logs ++ "ordinary-axioms.txt") expected
  IO.println "ORDINARY-COMPLETION-AXIOMS byte_identical=true sorryAx=false"
  IO.println "WARRANT bounded_completed_supplier=true narrowed_colon=true full_module=false critical_retirements=0"
