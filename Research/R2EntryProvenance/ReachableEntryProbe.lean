import L4YAML.Parser.Composition
import L4YAML.Proofs.Scanner.RegisterWitness

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.TokenParser
open L4YAML.Proofs.RegisterWitness

/- A source-initialized reachability control, not an observer of Prop proof terms.
   In particular this does not infer which disjunct a proof producer selected. -/
structure EntryReadings where
  steps : Nat := 0
  questions : List Nat := []
  dashes : Nat := 0
  explicitValues : Nat := 0
  explicitWithAncestors : Nat := 0
  preSequenceInnerValue : Nat := 0
  skippedQuestionOwners : Nat := 0
  deriving Repr

def event (name : String) (fields : List (String × Lean.Json)) : IO Unit :=
  IO.println ((Lean.Json.mkObj (("event", Lean.toJson name) :: fields)).compress)

def walkEntry (name input : String) : Nat → EntryReadings → ScannerState → IO EntryReadings
  | 0, _, _ => throw <| IO.userError s!"fuel exhausted: {name}"
  | fuel + 1, r, sc => do
    match scanNextToken_preprocess sc, scanNextToken sc with
    | .ok none, .ok none => return r
    | .ok (some (prep, c)), .ok (some out) =>
      let dis := if prep.allowDirectives then
        { prep with allowDirectives := false, documentEverStarted := true } else prep
      let isBlock := !prep.inFlow && (match scanNextToken_dispatchBlockIndicators dis c with
        | .ok (some _) => true
        | _ => false)
      let question := isBlock && c == '?'
      let dash := isBlock && c == '-'
      let kc := scanValueClearKey dis
      -- Exactly scanValue's explicitValue discriminator, restricted to block dispatch.
      let explicit := isBlock && c == ':' &&
        (kc.explicitKeyLine.isSome && !kc.simpleKey.possible &&
          (dis.inFlow || (dis.col : Int) == kc.explicitKeyCol))
      let survivors := markedCols out
      let beforeSequence := explicit && prep.col == 2 && !survivors.isEmpty && r.dashes == 0
      let skippedOwner := explicit && !survivors.isEmpty &&
        (r.questions.getLast?.any (fun q => prep.col < q))
      if question || dash || explicit then
        event "landing" [
          ("case", Lean.toJson name), ("step", Lean.toJson r.steps),
          ("char", Lean.toJson (String.singleton c)), ("line", Lean.toJson prep.line),
          ("column", Lean.toJson prep.col), ("marks_before", Lean.toJson (markedCols sc)),
          ("marks_prepared", Lean.toJson (markedCols prep)), ("marks_after", Lean.toJson survivors),
          ("explicit_value", Lean.toJson explicit), ("questions_before", Lean.toJson r.questions),
          ("dashes_before", Lean.toJson r.dashes)]
      if explicit then
        unless out.implicitValueLine == sc.implicitValueLine do
          throw <| IO.userError s!"explicit discriminator disagrees with scanner stamp: {name}"
        unless !(prep.col ∈ survivors) do
          throw <| IO.userError s!"consumed own column remains marked: {name}"
      let r := { r with
        steps := r.steps + 1
        questions := if question then r.questions ++ [prep.col] else r.questions
        dashes := r.dashes + (if dash then 1 else 0)
        explicitValues := r.explicitValues + (if explicit then 1 else 0)
        explicitWithAncestors := r.explicitWithAncestors + (if explicit && !survivors.isEmpty then 1 else 0)
        preSequenceInnerValue := r.preSequenceInnerValue + (if beforeSequence then 1 else 0)
        skippedQuestionOwners := r.skippedQuestionOwners + (if skippedOwner then 1 else 0) }
      walkEntry name input fuel r out
    | _, .error e => throw <| IO.userError s!"scanner failed: {name}: {e}"
    | _, _ => throw <| IO.userError s!"preprocess/step disagree: {name}"

def main : IO Unit := do
  let cases := [
    ("owner-witness", "? ? a\n  : - b"),
    ("owner-witness-complete", "? ? a\n  : - b\n: c"),
    ("sibling-after-value", "? ? a\n  : - b\n    - c\n: d"),
    ("nested-after-value", "? ? a\n  : -\n      - b\n: c"),
    ("compact-after-value", "? ? a\n  : - - b\n: c"),
    ("sequence-key", "? ? - a\n  : - b\n: c"),
    ("sibling-key", "? ? -\n    - a\n  : - b\n: c"),
    ("nested-key", "? ? -\n      - a\n  : - b\n: c"),
    ("compact-key", "? ? - - a\n  : - b\n: c"),
    ("skip-inner-question", "? ? ? a\n  : - b\n: c"),
    ("three-explicit-values", "? ? ? a\n    : - b\n  : - c\n: d"),
    ("implicit-colon-control", "? a: b\n: c"),
    ("flow-control", "[a, {b: c}]"),
    ("root-control", "- a\n- b")]
  let mut accepted := 0
  let mut preSequence := 0
  let mut ancestorValues := 0
  let mut skippedOwners := 0
  for (name, input) in cases do
    let parsed := (parseYaml input).isOk
    event "input" [("case", Lean.toJson name), ("source", Lean.toJson input),
      ("parser_accepts", Lean.toJson parsed)]
    unless parsed do throw <| IO.userError s!"control rejected by parser: {name}"
    accepted := accepted + 1
    let initial := (ScannerState.mk' input).emit .streamStart
    let r ← walkEntry name input (4 * input.length + 32) {} initial
    if name == "owner-witness" || name == "owner-witness-complete" then
      unless r.questions == [0, 2] && r.preSequenceInnerValue == 1 do
        throw <| IO.userError s!"owner witness did not establish predicted route order: {repr r}"
    if name == "skip-inner-question" then
      unless r.questions == [0, 2, 4] && r.preSequenceInnerValue == 1 && r.skippedQuestionOwners == 1 do
        throw <| IO.userError s!"skipped owner witness did not reach its predicted landing: {repr r}"
    preSequence := preSequence + r.preSequenceInnerValue
    ancestorValues := ancestorValues + r.explicitWithAncestors
    skippedOwners := skippedOwners + r.skippedQuestionOwners
  unless preSequence ≥ 5 && ancestorValues ≥ 9 do
    throw <| IO.userError "insufficient positive coverage"
  event "summary" [("accepted", Lean.toJson accepted),
    ("explicit_values_with_ancestors", Lean.toJson ancestorValues),
    ("inner_values_before_any_sequence", Lean.toJson preSequence),
    ("value_landings_below_last_question_with_ancestors", Lean.toJson skippedOwners),
    ("proof_disjunct_observation", Lean.toJson false),
    ("critical_retirement_claimed", Lean.toJson false)]
