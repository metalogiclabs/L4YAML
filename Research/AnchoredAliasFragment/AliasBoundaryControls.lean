module
public import Tests.Guards.Proofs.AnchoredWordAliasProbe
public meta import Tests.Guards.Proofs.AnchoredWordAliasProbe
public section
namespace L4YAML.Tests.Guards.AliasBoundaryControls
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Tests.Guards.AnchoredWordAliasProbe

-- Blueprint 7.7: additional boundaries before the unbounded later-alias proof.
def checkBoundary (k v : String) : IO Unit := do
 check k v
 let text := source k v
 let initial := (ScannerState.mk' text).emit .streamStart
 for fuel in [0,1,2,9] do
  unless !(scanLoop initial fuel).isOk do throw <| IO.userError s!"insufficient fuel {fuel} accepted"
 unless (scanLoop initial 10).isOk do throw <| IO.userError "ten-step fold refused"
 match scanFiltered text with
 | .ok ts =>
   unless ts.toList.map (·.val) == [.streamStart,.blockMappingStart,.key,.scalar k .plain,
     .value,.anchor "a",.scalar v .plain,.key,.scalar "copy" .plain,.value,.alias "a",.blockEnd,.streamEnd] do
     throw <| IO.userError "wrong exact alias token payloads"
   let positions := ts.toList.map fun t => (t.pos.offset,t.pos.line,t.pos.col)
   let b := k.length+v.length
   unless positions == [(0,0,0),(0,0,0),(0,0,0),(2,0,2),(3+k.length,1,0),
    (5+k.length,1,2),(8+k.length,1,5),(9+b,2,0),(11+b,2,2),(16+b,3,0),
    (18+b,3,2),(20+b,3,4),(20+b,3,4)] do throw <| IO.userError "wrong alias source positions"
 | .error _ => throw <| IO.userError "alias token scan refused"

def main : IO Unit := do
 let mut count := 0
 for k in ["copy","true","null","a","value"] do
  for v in ["copy","true","null","value","a"] do
   if k=="a" && v=="a" then continue -- already in the original 676 singleton pairs
   checkBoundary k v
   count:=count+1
 IO.println s!"ALIAS_BOUNDARY_CONTROLS pass={count} exact_positions=true fuels=0,1,2,9,10 duplicate_copy_key=true"
#eval main
end L4YAML.Tests.Guards.AliasBoundaryControls
