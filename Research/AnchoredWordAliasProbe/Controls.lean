module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Serialization.TokenEvents
public section
namespace L4YAML.Tests.Guards.AnchoredWordAliasProbe
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TokenEvents

-- Blueprint 7.7 next-fragment experiment. The positive state is reached from
-- actual initialization. Removing/renaming its registry is a causal ablation,
-- deliberately not a claim that those altered states are reachable.
def source (k v : String) : String := "? " ++ k ++ "\n: &a " ++ v ++ "\n? copy\n: *a"

def rejectsUndefined (r : Except ScanError (Option ScannerState)) : Bool :=
 match r with
 | .error (.undefinedAlias name _ _) => name == "a"
 | _ => false

def reachAlias (s : ScannerState) : Nat → IO Unit
 | 0 => throw <| IO.userError "alias not reached within fuel"
 | fuel+1 => do
  match scanNextToken_preprocess s with
  | .ok (some (_, '*')) =>
    match scanNextToken s with
    | .ok (some out) =>
      unless out.offset == s.input.utf8ByteSize do throw <| IO.userError "alias did not reach EOF"
      unless s.definedAnchors == #["a"] do throw <| IO.userError "wrong reachable registry"
      unless rejectsUndefined (scanNextToken {s with definedAnchors:=#[]}) do
        throw <| IO.userError "registry deletion did not prevent alias consumption"
      unless rejectsUndefined (scanNextToken {s with definedAnchors:=#["b"]}) do
        throw <| IO.userError "registry rename did not prevent alias consumption"
      unless (scanNextToken {s with definedAnchors:=#["a"]}).isOk do
        throw <| IO.userError "registry restoration did not restore alias consumption"
    | _ => throw <| IO.userError "actual reachable alias rejected"
  | .ok (some _) =>
    match scanNextToken s with
    | .ok (some t) => reachAlias t fuel
    | _ => throw <| IO.userError "actual source failed before alias"
  | _ => throw <| IO.userError "alias preprocessing failed"

def check (k v : String) : IO Unit := do
 let text := source k v
 let expected := YamlValue.mapping .block #[(YamlValue.plainScalar k,YamlValue.plainScalar v),
   (YamlValue.plainScalar "copy",YamlValue.plainScalar v)]
 let rawExpected := YamlValue.mapping .block #[(YamlValue.plainScalar k,
    YamlValue.scalar {content:=v,style:=.plain,anchor:=some "a"}),
   (YamlValue.plainScalar "copy",YamlValue.alias "a")]
 match parseYamlSingle text,parseYamlSingleRaw text,scanFiltered text with
 | .ok value,.ok raw,.ok tokens =>
   unless beqYamlValue value expected do throw <| IO.userError "wrong alias-composed payload"
   unless beqYamlValue raw.value rawExpected do throw <| IO.userError "raw anchor/alias payload changed"
   unless tokenEvents tokens == [.defineAnchor "a",.useAlias "a"] do
     throw <| IO.userError "wrong ordered nonempty trace"
 | _,_,_ => throw <| IO.userError "source/parser rejected alias fragment"
 reachAlias ((ScannerState.mk' text).emit .streamStart) 20

def main : IO Unit := do
 let mut count := 0
 for k in List.range 26 do
  for v in List.range 26 do
   check (String.singleton (Char.ofNat (97+k))) (String.singleton (Char.ofNat (97+v)))
   count:=count+1
 for n in [1,2,31,1023,1024,1025,2048] do
  for m in [1,1025,2048] do
   check (String.ofList (List.replicate n 'a')) (String.ofList (List.replicate m 'b'))
   count:=count+1
 IO.println s!"ANCHOR_ALIAS_PROBE pass={count} deleted_registry_rejected={count} renamed_registry_rejected={count} restored_registry_accepted={count} raw_and_composed_payloads=true ordered_events=true"
#eval main
end L4YAML.Tests.Guards.AnchoredWordAliasProbe
