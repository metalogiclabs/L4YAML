import Std

def parentBlocks : Array String := #[
  "Tests/Guards/Proofs/OwnerExplicitKeyPark.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyClosure.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyContent.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyFold.lean",
  "Tests/Guards/Proofs/OwnerExplicitKeyTransport.lean",
  "Tests/Guards/Proofs/OwnerKeyReplayAudit.lean"]

def extractParent (text path : String) : Except String String := do
  let marker := "          cat > " ++ path ++ " <<'LEAN'"
  let lines := text.splitOn "\n"
  unless (lines.filter (· == marker)).length == 1 do throw s!"nonunique parent block: {path}"
  let rest := (lines.dropWhile (· != marker)).drop 1
  let body := rest.takeWhile (· != "          LEAN")
  unless (rest.drop body.length).head? == some "          LEAN" do throw s!"unclosed parent block: {path}"
  let stripped ← body.mapM fun line =>
    if line.startsWith "          " then pure (line.drop 10).toString
    else if line.isEmpty then pure ""
    else throw s!"unexpected parent source indentation: {path}"
  pure (String.intercalate "\n" stripped ++ "\n")

def main (args : List String) : IO Unit := do
  let [evidence, owner] := args | throw (IO.userError "usage: PrepareParent.lean EVIDENCE OWNER")
  let root := System.FilePath.mk evidence
  let target := System.FilePath.mk owner
  let workflow ← IO.FS.readFile (root / ".github/workflows/group77-owner-key-replay.yml")
  for path in parentBlocks do
    let source ← match extractParent workflow path with
      | .ok text => pure text
      | .error message => throw (IO.userError message)
    let dest := target / path
    IO.FS.createDirAll (dest.parent.getD ".")
    IO.FS.writeFile dest source
  for name in #["OwnerExplicitKeyFreshTransport.lean", "OwnerExplicitKeyConsume.lean"] do
    IO.FS.writeFile (target / "Tests/Guards/Proofs" / name)
      (← IO.FS.readFile (root / "Research/ExplicitKeyContentConsumer" / name))
  for entry in ← (root / "Research/ExplicitWordFragment/Proofs").readDir do
    if entry.fileName.endsWith ".lean" then
      IO.FS.writeFile (target / "Tests/Guards/Proofs" / entry.fileName) (← IO.FS.readFile entry.path)
  IO.FS.createDirAll (target / "tools")
  IO.FS.writeFile (target / "tools/ExplicitWordReplayMain.lean")
    (← IO.FS.readFile (root / "Research/ExplicitWordFragment/ExplicitWordReplayMain.lean"))
  IO.println "EXACT_PARENT_SOURCES_RESTORED"
