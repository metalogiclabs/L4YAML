module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Serialization.TokenEvents
public section
namespace L4YAML.Tests.Guards.AnchoredWordControls
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TokenEvents

def source (k v : String) : String := "? " ++ k ++ "\n: &a " ++ v

def checkEOF (s : ScannerState) : Nat → IO Unit
  | 0 => throw <| IO.userError "EOF fuel exhausted"
  | fuel+1 => do
    match scanNextToken s with
    | .ok (some t) => checkEOF t fuel
    | .ok none =>
      match skipToContent s with
      | .ok t => unless !t.hasMore && t.peek? == none && t.offset == s.input.utf8ByteSize do
          throw <| IO.userError "unconsumed source"
      | .error _ => throw <| IO.userError "terminal whitespace failed"
    | .error _ => throw <| IO.userError "source scanner rejected anchored fragment"

def check (k v : String) : IO Unit := do
  let text := source k v
  let plain := YamlValue.mapping .block #[(YamlValue.plainScalar k, YamlValue.plainScalar v)]
  let anchored := YamlValue.mapping .block #[(YamlValue.plainScalar k,
    YamlValue.scalar { content := v, style := .plain, anchor := some "a" })]
  match parseYamlSingle text with
  | .ok actual => unless beqYamlValue actual plain do throw <| IO.userError s!"wrong composed mapping: {repr text}"
  | .error _ => throw <| IO.userError s!"composed fragment rejected: {repr text}"
  match parseYamlSingleRaw text with
  | .ok actual => unless beqYamlValue actual.value anchored do throw <| IO.userError s!"anchor lost before composition: {repr text}"
  | .error _ => throw <| IO.userError "raw fragment rejected"
  match scanFiltered text with
  | .ok ts =>
    unless tokenEvents ts == [.defineAnchor "a"] do throw <| IO.userError "nonempty event trace changed"
    unless ts.toList.map (·.val) == [.streamStart,.blockMappingStart,.key,.scalar k .plain,
      .value,.anchor "a",.scalar v .plain,.blockEnd,.streamEnd] do throw <| IO.userError "wrong token payloads"
    let positions := ts.toList.map fun t => (t.pos.offset,t.pos.line,t.pos.col)
    let endPos := (8+k.length+v.length,1,5+v.length)
    unless positions == [(0,0,0),(0,0,0),(0,0,0),(2,0,2),(3+k.length,1,0),
      (5+k.length,1,2),(8+k.length,1,5),endPos,endPos] do throw <| IO.userError "wrong positioned tokens"
  | .error _ => throw <| IO.userError "filtered scan failed"
  let initial := (ScannerState.mk' text).emit .streamStart
  for fuel in [0,1,2,5] do
    unless !(scanLoop initial fuel).isOk do throw <| IO.userError s!"insufficient fuel {fuel} admitted"
  unless (scanLoop initial 6).isOk do throw <| IO.userError "six-step fold failed"
  checkEOF initial (text.length+10)

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
      count := count+1
  for bad in ["? a\n: & b","? a\n: &a &b b"] do
    unless !(parseYamlSingle bad).isOk do throw <| IO.userError "invalid property control accepted"
  let actual ← match scanFiltered (source "a" "b") with
    | .ok ts => pure (tokenEvents ts)
    | .error _ => throw <| IO.userError "negative-control source rejected"
  for wrong in [[],[.defineAnchor "b"],[.useAlias "a"]] do
    if actual == wrong then throw <| IO.userError "corrupted event payload accepted"
  IO.println s!"ANCHORED_WORD_CONTROLS pass={count} rejected_properties=2 negative_events=3 fuel_boundaries=5 exact_positions=true"

#eval main
end L4YAML.Tests.Guards.AnchoredWordControls
