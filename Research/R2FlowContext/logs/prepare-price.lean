import Lean

def once (s old new : String) : IO String := do
  unless (s.splitOn old).length == 2 do
    throw (IO.userError s!"nonunique source anchor ({(s.splitOn old).length-1}): {old.take 100}")
  pure (s.replace old new)

def main (args : List String) : IO Unit := do
  let [inputPath,outputPath] := args | throw (IO.userError "expected parent and output")
  let mut s ← IO.FS.readFile inputPath
  let [before,routes] := s.splitOn "structure FlowBaseRoutes "
    | throw (IO.userError "flow routes declaration")
  let routes :: after := routes.splitOn "/-- **Kinds index (9b(i))**."
    | throw (IO.userError "flow routes end")
  let old := "SSLComments sp_ne sp_mid → SLYamlStream sp_start sp_mid"
  unless (routes.splitOn old).length == 3 do throw (IO.userError "two value declarations required")
  s := before ++ "structure FlowBaseRoutes " ++
    routes.replace old "SSLComments sp_ne sp_mid → R2Mandatory.Full s0 sp_start sp_mid" ++
    "/-- **Kinds index (9b(i))**." ++ String.intercalate "/-- **Kinds index (9b(i))**." after
  s ← once s "SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m) →\n      FlowStackB sp_start n"
    "SSLComments sp_ne sp_m → R2Mandatory.Full s' sp_start sp_m) →\n      FlowStackB sp_start n"
  let reader := "fun hnd hui sp_m h_ssl => resume.value\n"
  unless (s.splitOn reader).length == 3 do throw (IO.userError "two actual flow-close readers required")
  s := s.replace reader "fun hnd hui sp_m h_ssl => (resume.value\n"
  for (kind,grammar) in [("Sequence","flowSeq"),("Mapping","flowMap")] do
    let oldEnd := "sp_tok sp_m (SFlowContent." ++ grammar ++ " _ _ _ _ h_" ++
      (if kind == "Sequence" then "seq" else "map") ++ ") h_ssl)"
    let newEnd := oldEnd.dropEnd 1 |>.toString
    s ← once s oldEnd (newEnd ++ ").of_eq\n" ++
      "                      ((L4YAML.Proofs.PendingKeysStable.scanFlow" ++ kind ++ "End_preserves_pendingKeys s_ad).trans (h_pk_ad.trans h_pk_park))\n" ++
      "                      ((L4YAML.Proofs.EmitterScannability.scanFlow" ++ kind ++ "End_preserves_indents s_ad).trans (h_ind_ad.trans h_ind_park)))")
  IO.FS.writeFile outputPath s
  IO.println "PREPARED existing_flow_value_answer=Full existing_scanner_index=s0 close_readers=2"
