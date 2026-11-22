/- Exact native observations for the Group 7.7 grammar admission witness.
   These executable guards do not prove grammar nonmembership. -/
module
public import Tests.Guards.Proofs.UpstreamColonTrace
public import L4YAML.Scanner.Scanner
public import L4YAML.Parser.TokenParser
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket

namespace L4YAML.Tests.Guards.UpstreamColonTrace
open L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TokenEvents

def nativeObservation : Bool × Bool × Bool :=
  match scanFiltered input with
  | .error _ => (false, false, false)
  | .ok ts =>
    (true, (tokenEvents ts).isEmpty,
      match parseStream ts with | .error _ => true | .ok _ => false)

-- scanner succeeds / actual scanner events are [] / token parser refuses.
#guard nativeObservation == (true, true, true)
#eval nativeObservation

-- A legitimate complete empty stream remains a scanner/parser acceptance control.
#guard (match scanFiltered "" with
  | .error _ => false
  | .ok ts => match parseStream ts with | .ok _ => true | .error _ => false)

end L4YAML.Tests.Guards.UpstreamColonTrace
end Blanket
