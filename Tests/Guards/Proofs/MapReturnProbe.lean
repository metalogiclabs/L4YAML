/- Capstone 7.7: native scope checks before the paired mapping producer.
The protected adversarial source is unchanged. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
public meta import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
namespace L4YAML.Tests.Guards.MapReturnProbe
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
private def accepted (key : String) : Bool :=
  match scan (key ++ ": [b]\n...\n%YAML 1.2\n---\ny") with
  | .ok ts => (goOut ts.toList []).1.getLast? == some .beginDocument
  | .error _ => false
#guard (["a", "\"a\"", "'a'", "[a]", "{a: b}", "&x [a]", "!<tag:x> a", "[&a x, *a]"] : List String).all accepted
#guard (["[a,\n b]", "'a\n b'", "\"a\n b\""] : List String).all (fun k => !accepted k)
#guard ([0, 1, 2] : List Nat).all (fun fuel =>
  match scanLoop (scanSeed "a: [b]\n...\n%YAML 1.2\n---\ny") fuel with
  | .error _ => true | .ok _ => false)
end L4YAML.Tests.Guards.MapReturnProbe
