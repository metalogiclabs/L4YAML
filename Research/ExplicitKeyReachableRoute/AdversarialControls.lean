module
public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Serialization.TokenEvents
public meta import L4YAML.Scanner.Scanner
public meta import L4YAML.Proofs.Serialization.TokenEvents
public section
namespace Tests.AdversarialInstantiation.OwnerReachableQuestion
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.Serialization.TokenEvents

-- Run before attempting the producer proof. These are native initial states,
-- not fabricated explicit-key reservations. Fuel 0/1/2 exercises the actual
-- scanLoop entrance; no successful zero-fuel branch is expected.
def run : IO Unit := do
  let mut questions := 0
  let mut offers := 0
  let mut excluded := 0
  let mut smallFuel := 0
  let mut refusedTabs := 0
  let mut scalarChains := 0
  for lead in #["", "\n", "# lead\n", " \n# lead\r\n", "  ", "\n  ", "\uFEFF", "\uFEFF# lead\n", "\uFEFF\n  "] do
    for key in #["a", "'a'", "\"a\"", "&x a", "!foo a", "|-\n    a", ">-\n    a", "[a,b]", "{a: b}", ""] do
      let input := lead ++ "? " ++ key ++ "\n" ++ (if lead.endsWith "  " then "  " else "") ++ ": b"
      let raw := (ScannerState.mk' input).emit .streamStart
      let seed := match raw.peek? with | some '\uFEFF' => raw.consumeBOM | _ => raw
      for fuel in #[0, 1, 2] do
        match scanLoop seed fuel with
        | .ok _ => smallFuel := smallFuel + 1
        | .error _ => pure ()
      match scanNextToken_preprocess seed, scanNextToken seed with
      | .ok (some (p, '?')), .ok (some out) =>
        let ad := if p.allowDirectives then
          { p with allowDirectives := false, documentEverStarted := true } else p
        match scanNextToken_dispatchBlockIndicators ad '?' with
        | .ok (some direct) =>
          unless reprStr direct == reprStr out do
            throw (IO.userError "question dispatch differs from complete native step")
        | _ => throw (IO.userError "question dispatch failed hypothesis")
        unless !p.inFlow && !p.needIndentCheck && out.explicitKeyLine == some p.line &&
            out.explicitKeyCol == (p.col : Int) && lastRealTokenVal? out.tokens == some .key do
          throw (IO.userError "native question producer theorem-refuted")
        for pending in [[], ["!h!"], ["!x!", "!h!"]] do
          unless goOut out.tokens.toList pending == goOut seed.tokens.toList pending do
            throw (IO.userError "question event transport theorem-refuted")
        questions := questions + 1
        match scanNextToken_preprocess out with
        | .ok (some (land, _)) =>
          unless land.indents[0]? == some {column := -1, isSequence := false} do
            throw (IO.userError "question landing lost native sentinel")
          offers := offers + 1
        | _ => excluded := excluded + 1
        if key == "a" || key == "'a'" || key == "\"a\"" then
          match scanNextToken out with
          | .ok (some keyOut) =>
            match scanNextToken_preprocess keyOut, scanNextToken keyOut with
            | .ok (some (colon, ':')), .ok (some valuePark) =>
              unless colon.col == p.col && p.col < keyOut.col &&
                  lastRealTokenVal? valuePark.tokens == some .value do
                throw (IO.userError "native matched colon chain theorem-refuted")
              match scanNextToken valuePark with
              | .ok (some value) =>
                match scanNextToken_preprocess value with
                | .ok none => scalarChains := scalarChains + 1
                | _ => throw (IO.userError "scalar-chain EOF was not reached")
              | _ => throw (IO.userError "scalar-chain value dispatch failed")
            | _, _ => throw (IO.userError "scalar-chain colon dispatch failed")
          | _ => throw (IO.userError "scalar-chain key dispatch failed")
      | _, _ => throw (IO.userError s!"positive question failed hypothesis: {repr input}")
  for input in #["", "a", "?a", "[? a: b]", "---\n? a\n: b"] do
    let seed := (ScannerState.mk' input).emit .streamStart
    match scanNextToken_preprocess seed, scanNextToken seed with
    | .ok (some (p, '?')), .ok (some _) =>
      if isKeyCandidate p then throw (IO.userError "non-question negative control admitted")
      excluded := excluded + 1
    | _, _ => excluded := excluded + 1
  for lead in #["\t", " \t", "\n\t"] do
    match scanNextToken ((ScannerState.mk' (lead ++ "? a\n: b")).emit .streamStart) with
    | .error _ => refusedTabs := refusedTabs + 1
    | _ => throw (IO.userError "tab-indentation negative control admitted")
  unless questions == 90 && offers > 0 && excluded ≥ 5 && refusedTabs == 3 && scalarChains == 27 do
    throw (IO.userError "native question controls were vacuous")
  IO.println s!"OWNER_REACHABLE_QUESTION_CONTROLS questions={questions} next_landings={offers} scalar_chains_to_eof={scalarChains} excluded={excluded} small_fuel_success={smallFuel} tabs_refused={refusedTabs} theorem_refuted=0"
end Tests.AdversarialInstantiation.OwnerReachableQuestion
#eval Tests.AdversarialInstantiation.OwnerReachableQuestion.run
