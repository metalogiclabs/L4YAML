import Std

/- Reuse the six exact Lean source blocks in the independently qualified
   predecessor workflow. No workflow command is executed. Only these listed
   paths can be written, and each source block must occur exactly once. -/
def predecessorPaths : Array String := #[
  "Tests/Guards/Proofs/OwnerExplicitKeyPark.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyClosure.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyContent.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyFold.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyTransport.lean",
  "Tests/Guards/Proofs/OwnerKeyReplayAudit.lean"]

def extractPredecessor (text path : String) : Except String String := do
  let marker := "          cat > " ++ path ++ " <<'LEAN'"
  let lines := text.splitOn "\n"
  unless (lines.filter (· == marker)).length == 1 do
    throw s!"source marker must occur exactly once: {path}"
  let rest := (lines.dropWhile (· != marker)).drop 1
  let body := rest.takeWhile (· != "          LEAN")
  unless (rest.drop body.length).head? == some "          LEAN" do
    throw s!"unterminated source block: {path}"
  let stripped ← body.mapM fun line =>
    if line.startsWith "          " then pure (line.drop 10).toString
    else if line.isEmpty then pure ""
    else throw s!"source line lacks exact workflow indentation: {path}"
  pure (String.intercalate "\n" stripped ++ "\n")

def main (args : List String) : IO Unit := do
  let [workflow, target] := args
    | throw (IO.userError "usage: PreparePredecessor.lean WORKFLOW OWNER_CHECKOUT")
  let source ← IO.FS.readFile workflow
  for path in predecessorPaths do
    let text ← match extractPredecessor source path with
      | .ok text => pure text
      | .error message => throw (IO.userError message)
    let dest := (System.FilePath.mk target) / path
    IO.FS.createDirAll (dest.parent.getD ".")
    IO.FS.writeFile dest text
    IO.println s!"PREDECESSOR_SOURCE {path}"
