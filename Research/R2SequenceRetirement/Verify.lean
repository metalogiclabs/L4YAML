import Lean
open Lean

namespace R2SequenceRetirementVerify

def root := "Research/R2SequenceRetirement"

def readLog (name : String) : IO String := IO.FS.readFile (root ++ "/logs/" ++ name)

def errors (log : String) : List String :=
  log.splitOn "\n" |>.filter (·.contains ": error")

def main : IO Unit := do
  for name in ["mandatory-context.log", "geometry.log", "audit.log"] do
    if !(errors (← readLog name)).isEmpty then
      throw (IO.userError s!"positive module rejected: {name}")
  let audit ← readLog "audit.log"
  unless audit.contains "RETIREMENT-AUDIT roots=6 forbidden=4 root_context_premises=0" do
    throw (IO.userError "standalone dependency boundary absent")
  let reader ← readLog "reader-erasure.log"
  unless (errors reader).length == 1 && reader.contains "Application type mismatch" &&
      reader.contains "SLYamlStream start z" && reader.contains "Full sc start z" do
    throw (IO.userError "reader erasure did not reject at the declared boundary")
  let draft ← readLog "draft.log"
  let status ← IO.FS.readFile (root ++ "/logs/draft.exit")
  unless status.trimAscii.toString == "1" && (errors draft).length == 17 do
    throw (IO.userError "full changed-contract diagnostic boundary changed")
  unless draft.contains "MANDATORY-WRITER-AUDIT inventory=7 checked=6" &&
      draft.contains "context_contract=experimental global_acceptance=not_claimed critical_retirement=0" do
    throw (IO.userError "selected actual-writer audit absent")
  let checksum ← IO.Process.output {cmd := "sha256sum", args := #["--check", "--strict", root ++ "/EVIDENCE.sha256"]}
  unless checksum.exitCode == 0 do
    throw (IO.userError s!"evidence ledger failure: {checksum.stdout}{checksum.stderr}")
  let result := Json.mkObj [
    ("state", toJson "WARRANTED_COMPONENTS_AND_SELECTED_WRITERS; GLOBAL_MIGRATION_REJECTED"),
    ("accepted_standalone_modules", toJson (3 : Nat)),
    ("standard_axiom_dependency_roots", toJson (6 : Nat)),
    ("root_supplier_semantic_context_premises", toJson (0 : Nat)),
    ("initialized_geometry_kernel_facts", toJson (7 : Nat)),
    ("parser_acceptance_controls", toJson (4 : Nat)),
    ("reader_erasure_errors", toJson (1 : Nat)),
    ("actual_sequence_source_sites", toJson (7 : Nat)),
    ("selected_writer_terms_without_sorry_dependencies", toJson (6 : Nat)),
    ("writer_boundary", toJson "experimental stronger internal completion contract"),
    ("full_migration_accepts", toJson false),
    ("changed_contract_diagnostic_errors_not_debt_score", toJson (17 : Nat)),
    ("last_accepted_critical_positions", toJson (7 : Nat)),
    ("critical_retirements", toJson (0 : Nat)),
    ("fresh_candidate_census", toJson false),
    ("production_source_mutations", toJson (0 : Nat)),
    ("repository_qualification", toJson "NOT_RUN")]
  IO.FS.writeFile (root ++ "/result.json") (result.pretty ++ "\n")
  IO.println "SEQUENCE-RETIREMENT-CHECK modules=3 roots=6 writer_sites=6/7 reader_erasure=reject global_migration=reject critical_on=7 retired=0"

end R2SequenceRetirementVerify

def main := R2SequenceRetirementVerify.main
