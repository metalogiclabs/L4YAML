import Lean

def checkedProcess (command : String) (args : Array String) : IO String := do
  let result ← IO.Process.output {cmd := command, args := args}
  unless result.exitCode == 0 do throw (IO.userError (result.stdout ++ result.stderr))
  pure result.stdout

def main (args : List String) : IO Unit := do
  let [leanPath,parentPath,outputRoot] := args
    | throw (IO.userError "expected pinned Lean, reconstructed parent and output directory")
  IO.FS.createDirAll outputRoot
  let root := "Research/R2FlowContext/"
  let price := outputRoot ++ "/price.lean"
  let three := outputRoot ++ "/three.lean"
  let template := outputRoot ++ "/template.lean"
  discard <| checkedProcess leanPath #["--run",root ++ "logs/prepare-price.lean",parentPath,price]
  discard <| checkedProcess leanPath #["--run",root ++ "logs/prepare-three.lean",parentPath,three,"--fund-three"]
  IO.FS.writeFile three ((← IO.FS.readFile three) ++
    (← IO.FS.readFile (root ++ "logs/audit-before-axiom-subset.lean")))
  discard <| checkedProcess leanPath #["--run",root ++ "Prepare.lean",parentPath,template,"--fund-six"]
  let source ← IO.FS.readFile template
  let audit ← IO.FS.readFile (root ++ "ProductionAudit.inc.lean")
  unless source.endsWith audit do throw (IO.userError "current audit suffix absent")
  let body := (source.dropEnd audit.length).toString
  for (stage,file) in [("six","audit-six.lean"),("audit-first","audit-first.lean")] do
    IO.FS.writeFile (outputRoot ++ "/" ++ stage ++ ".lean")
      (body ++ (← IO.FS.readFile (root ++ "logs/" ++ file)))
  for (stage,expected) in [
      ("price","2b721bc94bde5140dff1d2099dc074db892d7df3d219654027732f33c6f3776e"),
      ("three","eef1d57907dfd6ea155bd21412841f24284f6de44dd3387a40bb7d3b7ca9a4b3"),
      ("six","900308bbd3a3abf8038d7dcc0e97c985e4124c8bf73eb19f91f6c6f870341f5a"),
      ("audit-first","d1aaa5b6054362691293dd1f526b7f2aa12166b57cef9ff484b69db82825814f")] do
    let digest ← checkedProcess "sha256sum" #[outputRoot ++ "/" ++ stage ++ ".lean"]
    unless digest.startsWith expected do throw (IO.userError (stage ++ " identity changed: " ++ digest))
  IO.println "LINEAGE reconstructed_sources=4 exact_hashes=4 compiler_verdicts_replayed=false"
