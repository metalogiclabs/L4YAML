/- Native controls for the return-carrying flow fold, before its proof.
Capstone 7.7 / S3. Protected AdversarialInstantiation remains unchanged. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
public meta import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.FlowReturnProbe
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
private def agreesFlow (body : String) (prior : List Event) : Bool :=
  match scan (body ++ "\n...\n%YAML 1.2\n---\ny") with
  | .ok ts => (goOut ts.toList []).1 == prior ++ [.endDocument, .beginDocument]
  | .error _ => false
#guard (["[]", "{}", "[a]", "{a: b}", "[[a], {b: c}]", "{a: [b, {c: d}]}",
  "[a,]", "{a: b,}", " [ ]", "[? a : b]", "[a: b]", "[: b]", "[a:]", "{? a : b}"] : List String).all
  (fun body => agreesFlow body [])
#guard agreesFlow "[&a x, *a]" [.defineAnchor "a", .useAlias "a"]
#guard agreesFlow "[&a [x], *a]" [.defineAnchor "a", .useAlias "a"]
#guard agreesFlow "[!<tag:x> [a]]" []
#guard agreesFlow "---\n[a]" [.beginDocument]
#guard agreesFlow "---\n{a: [b]}" [.beginDocument]
#guard agreesFlow "a: [b]" []
#guard ([0, 1, 2] : List Nat).all (fun fuel =>
  match scanLoop (scanSeed "[a]\n...\n%YAML 1.2\n---\ny") fuel with
  | .error _ => true | .ok _ => false)
end L4YAML.Tests.Guards.FlowReturnProbe
end Blanket
