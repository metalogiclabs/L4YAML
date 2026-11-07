module
import NormativeCommentCore
public meta import NormativeCommentCore
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch

namespace MathGraph.NormativeComments
open L4YAML

def indexedPaths (s : String) : List Bool := [
  (Scanner.Indexed.ScannerStateIx.scanIx s).isOk,
  (Scanner.Indexed.ScannerStateIx.scanWithCommentsIx s).isOk]

#guard forbidden.all fun n => (contexts (String.singleton (Char.ofNat n))).all
  fun s => (indexedPaths s).all (! ·)
#guard (["", "a", "\t", "é", "λ", "😀", "\u0085", "\u00a0", "\ufffd"] : List String).all
  fun body => (contexts body).all fun s => (indexedPaths s).all id
#guard (["\"\\x01\"", "\"#\\x01\"", "\"\u007f\"", "\"\u0080\"", "\"\uFEFF\""] : List String).all
  fun s => (indexedPaths s).all id
end MathGraph.NormativeComments
