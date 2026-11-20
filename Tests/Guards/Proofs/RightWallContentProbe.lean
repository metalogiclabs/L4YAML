/- Native probes for the next S3 producer, before its construction.
These are finite controls; the protected adversarial file is unchanged. -/
module

public import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
public meta import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed

@[expose] public section Blanket
namespace L4YAML.Tests.Guards.RightWallContentProbe

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed

private def agrees (src : String) (expected : List Event) : Bool :=
  match scan src with
  | .error _ => false
  | .ok ts => (goOut ts.toList []).1 == expected

#guard agrees "---\nx\n...\n%YAML 1.2\n---\ny"
  [.beginDocument, .endDocument, .beginDocument]
#guard agrees "--- x\n...\n%YAML 1.2\n---\ny"
  [.beginDocument, .endDocument, .beginDocument]
#guard agrees "---\n\"x\"\n...\n%YAML 1.2\n---\ny"
  [.beginDocument, .endDocument, .beginDocument]
#guard agrees "---\n'x'\n...\n%YAML 1.2\n---\ny"
  [.beginDocument, .endDocument, .beginDocument]
#guard agrees "---\n|\n x\n...\n%YAML 1.2\n---\ny"
  [.beginDocument, .endDocument, .beginDocument]
#guard agrees "---\n&a x\n...\n%YAML 1.2\n---\ny"
  [.beginDocument, .defineAnchor "a", .endDocument, .beginDocument]
#guard agrees "---\nx\n...\n%TAG !e! tag:x:\n---\n!e!y z"
  [.beginDocument, .endDocument, .beginDocument, .declareTag "!e!", .useTag "!e!"]

/- Falsification controls: each candidate extra-node/orphan-directive
counterexample is refused by the native scanner before a later directive
can be admitted. No grammar non-membership claim is inferred from a test. -/
private def rejectsBeforeNextDirective (body : String) : Bool :=
  match scan (body ++ "\n...\n%YAML 1.2\n---\nz") with
  | .error _ => true
  | .ok _ => false

#guard (["'x' 'y'", "---\n'x'\n'y'", "[,,]", "[,x]", "[x,,y]",
  "{,}", "{x: y,,z: w}", "&x &y z", "!x !y z",
  "%YAML 1.2", "%TAG !e! tag:x:", "%FOO",
  "---\n[x: y: z]", "---\n{x: y: z}"] : List String).all rejectsBeforeNextDirective

#guard ([0, 1, 2] : List Nat).all (fun fuel =>
  match scanLoop (scanSeed "---\nx\n...\n%YAML 1.2\n---\ny") fuel with
  | .error _ => true
  | .ok _ => false)

end L4YAML.Tests.Guards.RightWallContentProbe
end Blanket
