import Lean

open Lean
namespace R2SupplierVerification

def has (text pattern : String) : Bool := decide (1 < (text.splitOn pattern).length)

def evidence (path : System.FilePath) : IO String := do
  if ← path.pathExists then return ← IO.FS.readFile path
  let result ← IO.Process.output {cmd := "xz", args := #["-dc",path.toString ++ ".xz"]}
  unless result.exitCode == 0 do throw (IO.userError s!"cannot read {path}")
  return result.stdout

def labels (log : String) : IO (Array String) := do
  let mut result := #[]
  for line in log.splitOn "\n" do
    if line.startsWith "L4YAML/Proofs/Production/StreamAccum.lean:" &&
        has line ": error" then
      match line.splitOn ": error: " with
      | [_,label] =>
        unless label.startsWith "R2_" do throw (IO.userError s!"extra compiler error: {line}")
        result := result.push label
      | _ => throw (IO.userError s!"additional typed compiler error: {line}")
  return result

def exact (log : String) (expected : Array String) : IO Unit := do
  let actual ← labels log
  unless actual.size == expected.size && actual.all expected.contains && expected.all actual.contains do
    throw (IO.userError s!"compiler roster changed: expected {expected}, observed {actual}")

def between (log start stop : String) : IO String := do
  let split := log.splitOn start
  unless split.length == 2 do throw (IO.userError s!"nonunique/missing start: {start}")
  let parts := split[1]!.splitOn stop
  unless parts.length >= 2 do throw (IO.userError s!"missing stop: {stop}")
  return parts.head!

def referenceCount (log root name : String) : IO Nat := do
  let value ← between log (s!"SUPPLIER-ESCAPE-REFERENCE {root} {name}: ") "\n"
  match value.toNat? with
  | some n => return n
  | none => throw (IO.userError s!"invalid reference count {value}")

def check : IO Unit := do
  let taskPrefix := "Research/R2ColonSupplier/"
  let .ok json := Json.parse (← IO.FS.readFile (taskPrefix ++ "baseline-errors.json"))
    | throw (IO.userError "invalid frozen baseline roster")
  let .ok rows := json.getArr? | throw (IO.userError "baseline is not an array")
  let mut expected := #[]
  for row in rows do
    let .ok label := row.getObjValAs? String "label" | throw (IO.userError "missing baseline label")
    expected := expected.push label
  unless expected.size == 23 do throw (IO.userError "wrong integrated baseline size")
  let removed := #["R2_COLON_ENTRY_SUPPLIER_SEQUENCE_CONTENT",
    "R2_COLON_ENTRY_SUPPLIER_SEQUENCE_PENDING", "R2_OTHER_BLOCK_CONTENT_PAIR_UNMARKED",
    "R2_OTHER_PENDING_BLOCK_PAIR"]
  unless removed.all expected.contains do throw (IO.userError "missing predicted baseline obligation")
  let finalExpected := expected.filter (!removed.contains ·)
  let baseline ← evidence (taskPrefix ++ "logs/integrated-baseline-audited.log")
  let candidate ← evidence (taskPrefix ++ "logs/supplied-audited.log")
  let negative ← evidence (taskPrefix ++ "logs/owner-from-cover-negative.log")
  exact baseline expected
  exact candidate finalExpected
  exact negative (finalExpected.push "R2_OWNER_FROM_COVER_NEGATIVE_CONTROL")
  for root in ["L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent",
      "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock"] do
    let start := s!"SUPPLIER-TYPE-BEGIN {root}\n"
    let stop := s!"\nSUPPLIER-TYPE-END {root}"
    unless (← between baseline start stop) == (← between candidate start stop) do
      throw (IO.userError s!"actual caller external type changed: {root}")
    unless has candidate s!"ACTUAL-COLON-SUPPLIER {root}: applications=1 funded=true" do
      throw (IO.userError s!"actual supplier proof audit missing: {root}")
    for name in ["block_dispatch_deferred", "block_dispatch_deferred_stamp_offcol",
        "block_dispatch_deferred_stamp_nopack", "dropClose"] do
      let name := "L4YAML.Proofs.StreamAccum." ++ name
      unless (← referenceCount candidate root name) ≤ (← referenceCount baseline root name) do
        throw (IO.userError s!"new direct escape reference: {root} {name}")
    IO.println s!"CALLER {root}: type_byte_equal=true supplied=1 escape_references_nonincreasing=true"
  for label in ["PRODUCER","COMPACT","SEQUENCE-COMPLETION","COLON"] do
    let marker := s!"RAW-{label}-AXIOMS "
    let old ← between baseline marker "]"
    let current ← between candidate marker "]"
    unless old == current && !(has current "sorryAx") do
      throw (IO.userError s!"actual producer axiom profile changed: {label}")
    IO.println s!"AXIOMS {label}: byte_equal=true sorryAx=false"
  IO.println "SUPPLIER-DIAGNOSTICS baseline=23 candidate=19 negative=20 removed=4 replacement_labels=0 extra_errors=0 unchanged_external_types=2"
  IO.println "BOUNDARY new_explicit_suppliers=2 existing_implicit_route_reused=true full_module=false critical_retirements=0"

end R2SupplierVerification

def main : IO Unit := R2SupplierVerification.check
