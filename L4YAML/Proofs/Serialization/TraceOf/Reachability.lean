/- Capstone 7.7: the genuine native prefix relation, moved verbatim from
RightWallReachability so native producer proofs can consume it in production.
Its seed and step constructors are unchanged; no certificate is a premise. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
open L4YAML.Scanner
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
/-- Exactly the states visited by a finite prefix of the real scanner loop.
No successful-final-scan requirement hides a bad intermediate state. -/
inductive ScannerReachable (input : String) : ScannerState → Prop where
  | seed : ScannerReachable input (scanSeed input)
  | step {s t : ScannerState} : ScannerReachable input s →
      scanNextToken s = .ok (some t) → ScannerReachable input t

end L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
end Blanket
