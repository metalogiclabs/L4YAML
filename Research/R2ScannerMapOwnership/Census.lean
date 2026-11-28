import L4YAML.Proofs.Production.DocumentProduction
import Tests.Guards.Proofs.OrTrueAudit
import Scripts.Path.CapstonePath

open Lean Elab Command

-- Re-read the current environment. No pinned position or supply table is used
-- as an input. Supply counts are deliberately outside this directed ON check.
run_cmd do
  let env := (← getEnv).setExporting false
  liftTermElabM do
    let mut positions : Array Tests.Guards.OrTrueAudit.Pos := #[]
    for (name, moduleName) in ← Tests.Guards.OrTrueAudit.authored do
      positions := positions ++ (← Tests.Guards.OrTrueAudit.positionsOf name moduleName)
    let lines := (positions.map Tests.Guards.OrTrueAudit.posLine).toList
    let keys : Std.HashSet String := lines.foldl (fun acc line =>
      match Scripts.Path.CapstonePath.parsePos line with
      | some p => acc.insert s!"{p.decl}{p.site}"
      | none => acc) {}
    let reached := Scripts.Path.CapstonePath.reach env Scripts.Path.CapstonePath.roots
    let shown := Scripts.Path.CapstonePath.shownSet reached
    let drop := Std.HashSet.ofList (Scripts.Path.CapstonePath.dropSet.filter env.contains)
    let decls := reached.toArray.filter (fun name =>
      (`L4YAML.Proofs.StreamAccum).isPrefixOf name ||
      (`L4YAML.Proofs.PreprocessIndentStable).isPrefixOf name)
    let walked := Scripts.Path.CapstonePath.walkAll env drop keys decls
    let classed := Scripts.Path.CapstonePath.classify shown lines [] [] walked.arms walked.relays
    let critical := classed.filter (·.cls.startsWith "on-")
    let roster := critical.map (fun c =>
      s!"{c.pos.decl}{c.pos.site} {c.pos.kind} ∨ {c.pos.alt} {c.cls}") |>.qsort (· < ·)
    unless positions.size == 252 && critical.size == 7 do
      throwError "accepted directed census changed: positions={positions.size} critical={critical.size}"
    let some path ← IO.getEnv "R2_MAP_CENSUS_OUTPUT" | throwError "census output path required"
    IO.FS.writeFile path (Json.pretty (Json.mkObj [
      ("positions", toJson positions.size), ("critical_on", toJson critical.size),
      ("critical_roster", toJson roster), ("fresh_environment_positions", toJson true),
      ("supply_decline_counts_remeasured", toJson false),
      ("actual_arms", toJson walked.arms.size), ("actual_relays", toJson walked.relays.size)]))
    logInfo m!"ACCEPTED-MAP-CENSUS positions={positions.size} critical_on={critical.size} fresh_positions=true supply_counts=outside_boundary"
