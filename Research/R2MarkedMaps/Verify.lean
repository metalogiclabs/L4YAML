import Lean

open Lean

def main (_args : List String) : IO Unit := do
  let root := "Research/R2MarkedMaps/"
  let modules := ["adversarial", "writers", "stages", "reachable", "nativeboundary",
    "producers", "concrete", "dependencyaudit"]
  for name in modules do
    let log ← IO.FS.readFile s!"{root}logs/{name}.log"
    unless (← IO.FS.readFile s!"{root}logs/{name}.exit").trimAscii.toString == "0" &&
        !(log.contains ": error") && !(log.contains "sorryAx") do
      throw (IO.userError s!"module did not accept without sorryAx: {name}")
  let adversarial ← IO.FS.readFile s!"{root}logs/adversarial.log"
  unless adversarial.contains "MAP-ADVERSARIAL inputs=19 fuels=0,1,2,128 corrupted_sequence_mark=rejected" do
    throw (IO.userError "declared ownership controls absent")
  let audit ← IO.FS.readFile s!"{root}logs/dependencyaudit.log"
  unless audit.contains "required=7 forbidden=9 missing=0 free_premises=0 axioms=standard3" &&
      audit.contains "REACHABLE-PROJECTION-AUDIT inherited_native_leaves=4 independent_kernel_replays=4 new_axioms=0 semantic_context_still_required=true" &&
      audit.contains "MIGRATION-BOUNDARY production_module_unchanged=true eight_prior_demands_not_replayed=true critical_retirements=0" do
    throw (IO.userError "actual producer or universal-prefix boundary missing")
  let native ← IO.FS.readFile s!"{root}logs/nativeboundary.log"
  unless native.contains "NATIVE-BOUNDARY inherited_leaves=4 kernel_replays=4 replay_axioms=0 original_profiles_preserved=true" do
    throw (IO.userError "independent kernel replay of inherited leaves missing")
  IO.FS.writeFile s!"{root}result.json" (Json.pretty (Json.mkObj [
    ("state", toJson "WARRANTED_ACTUAL_PRODUCER_COMPOSITION; SUPERSEDED_DUPLICATE_OWNERSHIP; UNKNOWN_FULL_MIGRATION"),
    ("canonical_ownership_lineage", toJson "262952d4a31c46ba48c914714d40747f1f2e75e5"),
    ("new_ownership_discoveries", toJson (0 : Nat)),
    ("checked_modules", toJson (8 : Nat)),
    ("ownership_control_inputs", toJson (19 : Nat)),
    ("all_reachable_prefixes_have_mapping_marks", toJson true),
    ("actual_compact_question_rule_checked", toJson true),
    ("actual_explicit_colon_rule_checked", toJson true),
    ("initialized_actual_producer_root_free_premises", toJson (0 : Nat)),
    ("initialized_root_axioms", toJson ["propext", "Classical.choice", "Quot.sound"]),
    ("reachable_root_inherited_native_leaves", toJson (4 : Nat)),
    ("independent_kernel_replays_of_native_leaves", toJson (4 : Nat)),
    ("generic_semantic_context_preservation", toJson "UNKNOWN"),
    ("prior_full_diagnostic_demands", toJson (8 : Nat)),
    ("full_diagnostic_replayed_in_this_experiment", toJson false),
    ("critical_retirements", toJson (0 : Nat)),
    ("production_pr_ready", toJson false)]))
  IO.println "MAPS-RECEIPT modules=8 all_reachable_prefixes=true actual_question_and_colon=checked initialized_root=accepted inherited_native_leaves=4 kernel_replays=4 full_migration=unknown critical_retirements=0 pr_ready=false"
