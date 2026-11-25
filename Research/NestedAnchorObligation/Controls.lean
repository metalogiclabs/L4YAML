module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Serialization.TokenEvents
public import Std.Data.HashSet
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Serialization.TokenEvents
public meta import Std.Data.HashSet
public section
namespace L4YAML.Research.NestedAnchorObligation.Controls
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.Serialization.TokenEvents

-- Blueprint 7.7 preregistered experiment, executed before Transport.lean.
-- Target chain: reached scanner registry -> event/state correspondence ->
-- scan_trace -> corrected parse_iff_grammar. The latter two remain open.
structure Case where
  depth : Nat
  landing : Nat
  width : Nat
  explicit : Bool
  crlf : Bool
  comment : Bool
  name : String
  payload : String
deriving Repr

def pad (c : Case) (level : Nat) : String := String.ofList (List.replicate (level*c.width) ' ')
def eol (c : Case) : String := if c.crlf then "\r\n" else "\n"
def header (c : Case) (level : Nat) (key : String) : String :=
  if c.explicit then pad c level ++ "? " ++ key ++ eol c ++ pad c level ++ ":"
  else pad c level ++ key ++ ":"
def source (c : Case) : String := Id.run do
  let mut s := ""
  for i in List.range c.depth do
    s := s ++ header c i s!"n{i}" ++ eol c
  s := s ++ header c c.depth "target" ++ " &" ++ c.name ++ " " ++ c.payload
  if c.comment then s := s ++ " # retained anchor"
  return s ++ eol c ++ header c c.landing "copy" ++ " *" ++ c.name

def expected (c : Case) (raw : Bool) (wrong : Bool := false) : YamlValue := Id.run do
  let scalar := YamlValue.plainScalar c.payload
  let original := if raw then YamlValue.scalar {content:=c.payload,style:=.plain,anchor:=some c.name} else scalar
  let copied := if wrong then YamlValue.plainScalar (c.payload ++ "-wrong") else if raw then YamlValue.alias c.name else scalar
  let mut pairs := #[(YamlValue.plainScalar "target",original)]
  if c.landing == c.depth then pairs := pairs.push (YamlValue.plainScalar "copy",copied)
  let mut value := YamlValue.mapping .block pairs
  for i in (List.range c.depth).reverse do
    let mut outer := #[(YamlValue.plainScalar s!"n{i}",value)]
    if c.landing == i then outer := outer.push (YamlValue.plainScalar "copy",copied)
    value := .mapping .block outer
  return value

def undefined (name : String) : Except ScanError (Option ScannerState) → Bool
  | .error (.undefinedAlias n _ _) => n == name
  | _ => false

structure Reading where
  popSteps : Nat := 0
  poppedFrames : Nat := 0
  prepChecks : Nat := 0
deriving Inhabited

-- All positive states are reached by the real transition function from mk'.
-- Altered registries below are deliberate interventions, not reachability claims.
def walk (c : Case) (s : ScannerState) (r : Reading) : Nat → IO Reading
  | 0 => throw <| IO.userError "transition fuel exhausted"
  | fuel+1 => do
    match scanNextToken_preprocess s with
    | .ok (some (p,ch)) =>
      unless p.definedAnchors == s.definedAnchors do
        throw <| IO.userError "preprocessing changed the anchor registry"
      let dropped := s.indents.size-p.indents.size
      let r : Reading := { r with
        prepChecks := r.prepChecks + 1
        popSteps := r.popSteps + (if dropped > 0 then 1 else 0)
        poppedFrames := r.poppedFrames + dropped }
      if ch == '*' then
        unless p.definedAnchors == #[c.name] do throw <| IO.userError "wrong reached registry"
        unless r.poppedFrames == c.depth-c.landing do throw <| IO.userError "wrong dedentation witness"
        unless undefined c.name (scanNextToken {s with definedAnchors:=#[]}) do
          throw <| IO.userError "deletion did not reject alias"
        unless undefined c.name (scanNextToken {s with definedAnchors:=#["different-name"]}) do
          throw <| IO.userError "rename did not reject alias"
        unless (scanNextToken {s with definedAnchors:=#[c.name]}).isOk do
          throw <| IO.userError "restoration did not restore alias acceptance"
        match scanNextToken s with
        | .ok (some out) =>
          unless out.offset == s.input.utf8ByteSize do throw <| IO.userError "alias did not reach UTF-8 EOF"
          unless out.definedAnchors == #[c.name] do throw <| IO.userError "alias changed the registry"
          return r
        | _ => throw <| IO.userError "reached alias rejected"
      else
        match scanNextToken s with
        | .ok (some out) => walk c out r fuel
        | _ => throw <| IO.userError "source rejected before alias"
    | _ => throw <| IO.userError "preprocessing ended before alias"

def check (c : Case) : IO Reading := do
  let text := source c
  match parseYamlSingle text, parseYamlSingleRaw text, scanFiltered text with
  | .ok value,.ok raw,.ok tokens =>
    unless beqYamlValue value (expected c false) do throw <| IO.userError "composed payload mismatch"
    unless beqYamlValue raw.value (expected c true) do throw <| IO.userError "raw payload mismatch"
    if beqYamlValue value (expected c false true) then throw <| IO.userError "wrong-payload control accepted"
    unless tokenEvents tokens == [.defineAnchor c.name,.useAlias c.name] do
      throw <| IO.userError "ordered event mismatch"
  | _,_,_ => throw <| IO.userError "source/parser rejected nested family"
  let initial := (ScannerState.mk' text).emit .streamStart
  for fuel in [0,1,2] do
    match scanLoop initial fuel with
    | .error (.fuelExhausted _ _) => pure ()
    | _ => throw <| IO.userError "low-fuel control did not exhaust"
  walk c initial {} (text.utf8ByteSize*4+1)

def boundaryControls : IO Unit := do
  for sep in ["\n---\n", "\n...\n---\n"] do
    match scanFiltered ("root:\n  target: &a value" ++ sep ++ "copy: *a") with
    | .error (.undefinedAlias "a" _ _) => pure ()
    | _ => throw <| IO.userError "anchor leaked across document reset"
  let s := "root:\n  target: &a first\n  copy: *a\nother: &a second\ncopy: *a"
  let first := YamlValue.plainScalar "first"
  let second := YamlValue.plainScalar "second"
  let want := YamlValue.mapping .block #[(.plainScalar "root",.mapping .block #[(.plainScalar "target",first),(.plainScalar "copy",first)]),(.plainScalar "other",second),(.plainScalar "copy",second)]
  match parseYamlSingle s with
  | .ok got => unless beqYamlValue got want do throw <| IO.userError "redefinition did not use most recent anchor"
  | _ => throw <| IO.userError "redefinition source rejected"
  for text in ["", "copy: *a", "root:\n  copy: *a", "target: &a value\ncopy: *missing"] do
    if text.isEmpty then
      unless (scanFiltered text).isOk do throw <| IO.userError "empty control rejected"
    else
      match scanFiltered text with
      | .error (.undefinedAlias _ _ _) => pure ()
      | _ => throw <| IO.userError "undefined alias control accepted"

def main : IO Unit := do
  boundaryControls
  let mut count := 0
  let mut popCases := 0
  let mut pops := 0
  let mut checks := 0
  let mut sources : Std.HashSet String := {}
  for depth in [0,1,2,3,8,16] do
    for landing in ([0,depth/2,depth].eraseDups) do
      for width in [1,2,4] do
        for explicit in [false,true] do
          for crlf in [false,true] do
            for comment in [false,true] do
              for name in ["a","anchor-name","λ"] do
                for payload in ["v",String.ofList (List.replicate 31 'b'),"café"] do
                  let c : Case := ⟨depth,landing,width,explicit,crlf,comment,name,payload⟩
                  let r ← try check c catch e => throw <| IO.userError s!"{repr c}: {e}"
                  sources := sources.insert (source c)
                  count := count+1
                  if r.popSteps>0 then popCases := popCases+1
                  pops := pops+r.poppedFrames
                  checks := checks+r.prepChecks
  IO.println s!"NESTED_ANCHOR executions={count} distinct_sources={sources.size} actual_dedent_cases={popCases} popped_frames={pops} preprocessing_checks={checks} exact_raw=true exact_composed=true ordered_events=true"
  IO.println s!"NESTED_CONTROLS deletion={count} rename={count} restoration={count} wrong_payload_rejected={count} low_fuel={3*count} document_resets=2 redefinition=1 undefined_sources=3 empty=1"

end L4YAML.Research.NestedAnchorObligation.Controls

def main : IO Unit := L4YAML.Research.NestedAnchorObligation.Controls.main
