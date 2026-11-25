module
public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Proofs.Serialization.TokenEvents
public section
namespace Tests.AdversarialInstantiation.OwnerFreshTransportAdversarial
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.TokenEvents
private def tokAt (v : YamlToken) : Positioned YamlToken := ⟨default, v, default⟩
private def prefixes : Array (Array (Positioned YamlToken)) :=
  #[#[], #[tokAt (.anchor "a")], #[tokAt (.alias "a")], #[tokAt (.tag "!h!" "x")],
    #[tokAt (.tagDirective "!h!" "p")], #[tokAt .documentStart], #[tokAt .documentEnd],
    #[tokAt .placeholder], #[tokAt .blockMappingStart, tokAt .key],
    #[tokAt (.anchor "a"), tokAt (.alias "a"), tokAt (.tag "!h!" "x")],
    #[tokAt (.tagDirective "!h!" "p"), tokAt .documentStart, tokAt (.anchor "a")]]
private def pending : Array (List String) := #[[], ["!h!"], ["!x!", "!h!"]]
private def eqTrace (a b : Array (Positioned YamlToken)) : Bool :=
  pending.all fun p => goOut a.toList p == goOut b.toList p

def run : IO Unit := do
  let mut fresh := 0
  let mut drop := 0
  let mut vacuous := 0
  for ts in prefixes do
    for keyLine in #[none, some 1, some 2] do
      for col in #[0, 1, 3] do
        let s := { (ScannerState.mk' ": v") with
          tokens := ts, col := col,
          line := 2, simpleKeyAllowed := true, explicitKeyLine := keyLine,
          explicitKeyCol := col, indents := #[{column := -1, isSequence := false},
            {column := col, isSequence := false}] }
        let saved := closeStaleExplicitKey (saveSimpleKey s)
        match scanValue saved with
        | .error _ => vacuous := vacuous + 1
        | .ok s' =>
          unless eqTrace (saveSimpleKey s).tokens s'.tokens do
            throw (IO.userError "fresh reservation theorem-refuted")
          fresh := fresh + 1
    for txt in #["\n: v", "\r\n: v", " # c\n: v", "\n\n: v", "\n  : v"] do
      for col in #[3, 5] do
        for allowed in #[false, true] do
          for fuel in #[0, 1, 2] do
            let s := { (ScannerState.mk' txt) with
              tokens := ts, col := col,
              simpleKeyAllowed := allowed, needIndentCheck := false,
              indents := (#[{column := -1, isSequence := false}] ++
                (Array.replicate fuel {column := 0, isSequence := false})) }
            match scanNextToken_preprocess s with
            | .ok (some (p, ':')) =>
              match scanValue p with
              | .ok s' =>
                if p.col < s.col then
                  unless eqTrace s.tokens s'.tokens do
                    throw (IO.userError "decreasing-column transport theorem-refuted")
                  drop := drop + 1
                else vacuous := vacuous + 1
              | _ => vacuous := vacuous + 1
            | _ => vacuous := vacuous + 1
  -- An unreserved synthetic key CAN destroy an alias event. This negative
  -- control rejects the tempting universal statement with no provenance.
  let bad := { (ScannerState.mk' ": v") with
    tokens := #[tokAt (.alias "a"), tokAt .placeholder], simpleKeyAllowed := false,
    simpleKey := { possible := true, tokenIndex := 0, pos := default },
    indents := #[{column := -1, isSequence := false}] }
  match scanValue bad with
  | .error _ => throw (IO.userError "negative control did not reach scanValue")
  | .ok b =>
    if eqTrace bad.tokens b.tokens then
      throw (IO.userError "negative alias-overwrite control accepted")
  unless fresh > 0 && drop > 0 do throw (IO.userError "vacuous fresh transport controls")
  IO.println s!"OWNER_FRESH_TRANSPORT_CONTROLS fresh={fresh} col_drop={drop} failed_hypothesis={vacuous} theorem_refuted=0 negative_control=pass"
end Tests.AdversarialInstantiation.OwnerFreshTransportAdversarial

#eval Tests.AdversarialInstantiation.OwnerFreshTransportAdversarial.run
