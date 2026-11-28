import Lean

def main (args : List String) : IO Unit := do
  let [inputPath,outputPath] := args | throw (IO.userError "expected audited input and erased output")
  let source ← IO.FS.readFile inputPath
  let old := "exact h_wholeCompletedContext sp_mid h_ssl z\n        (SCompactSeqTail.cons k sp_mid _ sp_scan' e z h_ind h_dash2 h_gnot2 node tail))"
  let erased := "exact (h_wholeCompletedContext sp_mid h_ssl z\n        (SCompactSeqTail.cons k sp_mid _ sp_scan' e z h_ind h_dash2 h_gnot2 node tail)).close)"
  unless (source.splitOn old).length == 2 do throw (IO.userError "actual completed sibling reader is not unique")
  IO.FS.writeFile outputPath (source.replace old erased)
  IO.println "ERASED actual_completed_sibling_reader context_to_stream_only"
