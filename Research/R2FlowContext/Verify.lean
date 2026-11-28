import Lean

open Lean

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def readLog (name : String) : IO String := do
  let path := "Research/R2FlowContext/logs/" ++ name ++ ".log.xz.b64"
  let result ← IO.Process.output {cmd := "bash", args := #["-c",
    "set -euo pipefail; base64 --decode \"$1\" | xz --decompress --stdout", "r2-flow-log", path]}
  require (result.exitCode == 0) s!"cannot decode {path}"
  pure result.stdout

def errors (log : String) : List String :=
  (log.splitOn "\n").filter (·.contains ": error:")

def lineNumber (error : String) : IO Nat := do
  let some n := ((error.splitOn ":").getD 1 "").toNat?
    | throw (IO.userError s!"missing source coordinate {error}")
  pure n

def main : IO Unit := do
  let parent ← readLog "parent-draft"
  let price ← readLog "price"
  let three ← readLog "three"
  let six ← readLog "six"
  let audited ← readLog "audited"
  let erased ← readLog "erased"
  let lineage ← readLog "lineage"
  require (lineage.contains "LINEAGE reconstructed_sources=4 exact_hashes=4 compiler_verdicts_replayed=false")
    "failed-source reconstruction receipt absent"
  require ((errors parent).length == 17) "parent rejected boundary changed"
  require ((errors price).length == 23) "first flow price changed"
  require ((errors three).length == 21 && three.contains "flow transport axiom boundary [propext, Quot.sound]")
    "preserved first audit failure changed"
  require ((errors six).length == 17 && (errors audited).length == 17) "final positive rejection boundary changed"
  require ((errors erased).length == 18) "reader erasure is not one additional error"
  for name in ["price","three","six","audited","erased"] do
    let status ← IO.FS.readFile ("Research/R2FlowContext/logs/" ++ name ++ ".exit")
    require (status.trimAscii.toString == "1") s!"wrong compiler boundary {name}"
  let expected := [14456,14608,24914,25247,25279,25514,25522,25903,26325,26553,
    28794,36621,36659,36934,36939,36978,36987]
  let actual ← (errors audited).mapM lineNumber
  require (actual == expected) s!"unexpected positive diagnostic locations {actual}"
  let erasedLines ← (errors erased).mapM lineNumber
  let retained := expected.map (fun n => if n > 20700 then n-2 else n)
  for n in retained do require (erasedLines.contains n) s!"erasure changed existing residual {n}"
  let extra := erasedLines.filter (fun n => !retained.contains n)
  require (extra.length == 1 && extra.head! > 20700 && extra.head! < 20800)
    "erasure did not fail at actual sequence close"
  for log in [audited,erased] do
    require (log.contains "FLOW-WRITER-AUDIT expanded_fields=13 clean_fields=8 transported_fields=5")
      "actual flow writer inventory changed"
    require (log.contains "MANDATORY-WRITER-AUDIT inventory=7 checked=6 expanded_checked=7")
      "inherited sequence writer audit changed"
    require (log.contains "FLOW-CLOSE-AUDIT actual_reader=connected transport_axioms=#[`propext, `Quot.sound]")
      "actual reader or axiom audit absent"
  require (audited.contains "FLOW-CLOSE-FIELDS expanded=2 clean=2 transported=2") "positive actual close fields unclean"
  require (erased.contains "FLOW-CLOSE-FIELDS expanded=2 clean=1 transported=1") "erased close field remained clean"
  let result := Json.mkObj [
    ("state",toJson "WARRANTED_LOCAL_FLOW_TRANSPORT; UNKNOWN_FULL_MIGRATION"),
    ("parent",toJson "7a8da4626b2655370708800016439f3220a39468"),
    ("parent_draft_sha256",toJson "d3589230b768b92f8fac3df21535b7aa199a25f0f5228a4b67c65cf05ebcc193"),
    ("audited_source_sha256",toJson "416aa519de2d988a37364a05bf6768b03420d49b9781b352130a0987d57d1c6b"),
    ("erased_source_sha256",toJson "8fe4c5fc76c96e93a2b06ae7cf4c34b55518f8a697d253f8c209ad547b46159c"),
    ("expanded_flow_value_fields",toJson (13 : Nat)),
    ("sorry_free_flow_value_fields",toJson (8 : Nat)),
    ("transported_flow_value_fields",toJson (5 : Nat)),
    ("uncredited_existing_refutation_terms",toJson (3 : Nat)),
    ("shared_suffix_field_receives_clean_credit",toJson false),
    ("transported_field_forbidden_references_checked",toJson (4 : Nat)),
    ("equality_transport_axioms",toJson ["propext","Quot.sound"]),
    ("failed_sources_reconstructed_exactly",toJson (4 : Nat)),
    ("actual_close_field_terms_checked",toJson (2 : Nat)),
    ("reader_erasure_additional_errors",toJson (1 : Nat)),
    ("remaining_unique_flow_supply_sites",toJson ["generic fresh-document landing","deferred dropClose fallback"]),
    ("remaining_nonflow_errors",toJson (15 : Nat)),
    ("remaining_full_source_errors",toJson (17 : Nat)),
    ("initial_price_errors",toJson (23 : Nat)),
    ("net_global_retirement_credit",toJson (0 : Nat)),
    ("constructor_fields_added",toJson (0 : Nat)),
    ("public_context_premises_added",toJson (0 : Nat)),
    ("internal_geometry_premise_added",toJson "Mono sc; both existing callers discharge it"),
    ("new_initialized_examples_promoted",toJson (0 : Nat)),
    ("full_source_accepted",toJson false),
    ("full_qualification",toJson "NOT_RUN"),
    ("critical_positions_last_accepted",toJson (7 : Nat)),
    ("critical_retirements",toJson (0 : Nat)),
    ("production_pr_ready",toJson false)]
  IO.FS.writeFile "Research/R2FlowContext/result.json" (result.pretty ++ "\n")
  IO.println "VERIFIED transported_flow_fields=5 actual_close_fields=2 erasure_extra_errors=1 whole_source_errors=17 critical_retirements=0"
