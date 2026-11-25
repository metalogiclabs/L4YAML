module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Serialization.TokenEvents
public section
namespace L4YAML.Tests.Guards.AnchoredWordControls
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TokenEvents

def source (k v a : String) : String := "? " ++ k ++ "\n: &" ++ a ++ " " ++ v

def rawValue (k v a : String) : YamlValue :=
 .mapping .block #[(.scalar {content := k, style := .plain},
                    .scalar {content := v, style := .plain, anchor := some a})]

def composedValue (k v : String) : YamlValue :=
 .mapping .block #[(.scalar {content := k, style := .plain},
                    .scalar {content := v, style := .plain})]

def checkEOF (s : ScannerState) : Nat → Nat → IO Nat
 | 0, _ => throw <| IO.userError "EOF fuel exhausted"
 | fuel+1, count => do
   match scanNextToken s with
   | .ok (some t) => checkEOF t fuel (count+1)
   | .ok none =>
     match skipToContent s with
     | .ok t =>
       unless !t.hasMore && t.peek? == none do throw <| IO.userError "unconsumed source"
       return count
     | .error _ => throw <| IO.userError "terminal whitespace failed"
   | .error _ => throw <| IO.userError "source scanner rejected fragment"

def check (k v a : String) : IO Unit := do
 let text := source k v a
 match scanFiltered text with
 | .ok ts =>
   unless tokenEvents ts == [.defineAnchor a] do
     throw <| IO.userError s!"wrong anchor event: {repr text}"
   unless ts.toList.map (·.val) ==
    [.streamStart,.blockMappingStart,.key,.scalar k .plain,
     .value,.anchor a,.scalar v .plain,.blockEnd,.streamEnd] do
     throw <| IO.userError s!"wrong token shape or payload: {repr text}"
 | .error _ => throw <| IO.userError s!"filtered scan rejected: {repr text}"
 match parseYamlSingleRaw text with
 | .ok doc =>
   unless beqYamlValue doc.value (rawValue k v a) do
     throw <| IO.userError s!"wrong raw mapping or anchor attachment: {repr text}"
   unless doc.anchors.size == 1 do throw <| IO.userError "wrong anchor table size"
   let entry := doc.anchors[0]!
   unless entry.1 == a && beqYamlValue entry.2 (.scalar {content := v, style := .plain}) do
     throw <| IO.userError "wrong anchor table identity or cleaned value"
 | .error _ => throw <| IO.userError "raw parse rejected"
 match parseYamlSingle text with
 | .ok actual =>
   unless beqYamlValue actual (composedValue k v) do throw <| IO.userError "wrong composed mapping"
 | .error _ => throw <| IO.userError "composed parse rejected"
 let count ← checkEOF ((ScannerState.mk' text).emit .streamStart) (text.length+10) 0
 unless count == 5 do throw <| IO.userError s!"wrong number of native transitions: {count}"

def main : IO Unit := do
 let mut count := 0
 for ki in List.range 26 do
  for vi in List.range 26 do
   for ai in List.range 26 do
    check (String.singleton (Char.ofNat (97+ki))) (String.singleton (Char.ofNat (97+vi)))
      (String.singleton (Char.ofNat (97+ai)))
    count := count+1
 for k in ["alpha","null","true","abcdefghijklmnopqrstuvwxyz"] do
  for a in ["x","anchor","abcdefghijklmnopqrstuvwxyz"] do
   for n in [1,2,7,31,127,1023,1024,1025,2048] do
    check k (String.ofList (List.replicate n 'b')) a
    count := count+1
 for n in [1023,1024,1025,2048] do
  for m in [1,1025,2048] do
   for a in ["x","anchor",String.ofList (List.replicate 1025 'z')] do
    check (String.ofList (List.replicate n 'a')) (String.ofList (List.replicate m 'b')) a
    count := count+1
 let text := source "a" "b" "x"
 let ts ← match scanFiltered text with
  | .ok ts => pure ts
  | .error _ => throw <| IO.userError "negative-control source rejected"
 for wrong in [[],[.defineAnchor "y"],[.defineAnchor "x",.defineAnchor "x"]] do
  if tokenEvents ts == wrong then throw <| IO.userError "corrupted expected event trace accepted"
 let doc ← match parseYamlSingleRaw text with
  | .ok doc => pure doc
  | .error _ => throw <| IO.userError "negative-control raw source rejected"
 for wrong in [rawValue "a" "c" "x",rawValue "a" "b" "y",composedValue "a" "b"] do
  if beqYamlValue doc.value wrong then throw <| IO.userError "corrupted raw value accepted"
 IO.println s!"ANCHORED_WORD_CONTROLS pass={count} failed_hypothesis=3 refuted=0 negative_controls=6"
 IO.println "SCOPE: finite executable prerequisites; no unbounded anchored-fragment theorem claimed"
#eval main
end L4YAML.Tests.Guards.AnchoredWordControls
