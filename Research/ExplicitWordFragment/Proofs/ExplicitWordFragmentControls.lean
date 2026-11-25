module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Serialization.TokenEvents
public section
namespace L4YAML.Tests.Guards.ExplicitWordFragmentControls
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TokenEvents

def source (k v : String) : String := "? " ++ k ++ "\n: " ++ v

def checkEOF (s : ScannerState) : Nat → IO Unit
 | 0 => throw <| IO.userError "EOF fuel exhausted"
 | fuel+1 => do
   match scanNextToken s with
   | .ok (some t) => checkEOF t fuel
   | .ok none =>
     match skipToContent s with
     | .ok t => unless !t.hasMore && t.peek? == none do throw <| IO.userError "unconsumed source"
     | .error _ => throw <| IO.userError "terminal whitespace failed"
   | .error _ => throw <| IO.userError "source scanner rejected fragment"

def check (k v : String) : IO Unit := do
 let text := source k v
 let expected := YamlValue.mapping .block #[(YamlValue.plainScalar k, YamlValue.plainScalar v)]
 match parseYamlSingle text with
 | .ok actual => unless beqYamlValue actual expected do throw <| IO.userError s!"wrong mapping: {repr text}"
 | .error _ => throw <| IO.userError s!"fragment rejected: {repr text}"
 match scanFiltered text with
 | .ok ts =>
   unless tokenEvents ts == [] do throw <| IO.userError "unexpected serialization events"
   unless ts.toList.map (·.val) == [.streamStart,.blockMappingStart,.key,.scalar k .plain,
     .value,.scalar v .plain,.blockEnd,.streamEnd] do throw <| IO.userError "wrong token shape"
 | .error _ => throw <| IO.userError "filtered scan failed"
 checkEOF ((ScannerState.mk' text).emit .streamStart) (text.length+10)

def main : IO Unit := do
 let mut count := 0
 for k in List.range 26 do
  for v in List.range 26 do
   check (String.singleton (Char.ofNat (97+k))) (String.singleton (Char.ofNat (97+v)))
   count := count+1
 for k in ["alpha","null","true","abcdefghijklmnopqrstuvwxyz"] do
  for n in [1,2,7,31,127,1023,1024,1025,2048] do
   check k (String.ofList (List.replicate n 'b'))
   count := count+1
 for n in [1023,1024,1025,2048] do
  for m in [1,1025,2048] do
   check (String.ofList (List.replicate n 'a')) (String.ofList (List.replicate m 'b'))
   count:=count+1
 let actual ← match parseYamlSingle "? a\n: b" with
  | .ok value => pure value
  | .error _ => throw <| IO.userError "negative-control source rejected"
 for wrong in [YamlValue.mapping .block #[(YamlValue.plainScalar "b",YamlValue.plainScalar "a")],
    YamlValue.mapping .block #[(YamlValue.plainScalar "a",YamlValue.plainScalar "c")]] do
  if beqYamlValue actual wrong then throw <| IO.userError "corrupted expected mapping accepted"
 IO.println s!"EXPLICIT_WORD_FRAGMENT_CONTROLS pass={count} failed_hypothesis=0 refuted=0 negative_controls=2"
#eval main
end L4YAML.Tests.Guards.ExplicitWordFragmentControls
