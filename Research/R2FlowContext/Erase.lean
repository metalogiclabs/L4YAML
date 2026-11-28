import Lean

def main (args : List String) : IO Unit := do
  let [inputPath,outputPath] := args | throw (IO.userError "expected audited and erased sources")
  let source ← IO.FS.readFile inputPath
  let old := "sp_tok sp_m (SFlowContent.flowSeq _ _ _ _ h_seq) h_ssl).of_eq\n                      ((L4YAML.Proofs.PendingKeysStable.scanFlowSequenceEnd_preserves_pendingKeys s_ad).trans (h_pk_ad.trans h_pk_park))\n                      ((L4YAML.Proofs.EmitterScannability.scanFlowSequenceEnd_preserves_indents s_ad).trans (h_ind_ad.trans h_ind_park)))"
  let new := "sp_tok sp_m (SFlowContent.flowSeq _ _ _ _ h_seq) h_ssl).close)"
  unless (source.splitOn old).length == 2 do throw (IO.userError "actual sequence-close reader not unique")
  IO.FS.writeFile outputPath (source.replace old new)
  IO.println "ERASED actual_sequence_close_reader Full_to_stream_only"
