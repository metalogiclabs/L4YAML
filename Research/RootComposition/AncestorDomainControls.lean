module
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Scanner.RegisterWitness
public import L4YAML.Scanner.TokenQueries
public meta import L4YAML.Parser.Composition
public meta import L4YAML.Proofs.Scanner.RegisterWitness
public meta import L4YAML.Scanner.TokenQueries
public section

open L4YAML L4YAML.Scanner L4YAML.TokenParser L4YAML.Proofs.RegisterWitness

structure Readings where
  accepted : Nat := 0
  rejected : Nat := 0
  rootPreprocess : Nat := 0
  rootIndented : Nat := 0
  nonQuestionMarkedOwn : Nat := 0
  valueSlots : Nat := 0
  valueSlotOwnMarked : Nat := 0
  valueSlotAncestors : Nat := 0
  dashLandings : Nat := 0
  dashRightMarks : Nat := 0
  dashEqualMarks : Nat := 0
  deriving Repr

def lastReal (sc : ScannerState) : Option YamlToken :=
  (prevRealIdx? sc.tokens sc.tokens.size).map fun i => sc.tokens[i]!.val

def walk (input : String) (readings : IO.Ref Readings) :
    Nat → Nat → ScannerState → IO Unit
  | 0, _, _ => throw <| IO.userError "reachable-source traversal exhausted fuel"
  | fuel + 1, step, sc => do
    match scanNextToken_preprocess sc, scanNextToken sc with
    | .ok none, .ok none => pure ()
    | .ok (some (prep, c)), .ok (some out) =>
      if step == 0 then
        unless (markedCols sc).isEmpty && (markedCols prep).isEmpty do
          throw <| IO.userError s!"INITIAL_ROOT_DOMAIN_REFUTED {repr input}"
        readings.modify fun r => { r with
          rootPreprocess := r.rootPreprocess + 1
          rootIndented := r.rootIndented + (if 0 < prep.col then 1 else 0) }
      if !out.inFlow && 0 ≤ out.currentIndent then
        let own := out.currentIndent.toNat
        let marks := markedCols out
        let notQuestion := match lastReal out with
          | some .key | none => false
          | _ => true
        if notQuestion && own ∈ marks then
          let old ← readings.get
          if old.nonQuestionMarkedOwn < 4 then
            IO.println s!"TOKEN_ONLY_NOTQUESTION_REFUTED source={repr input} step={step} own={own} marks={marks} token={repr (lastReal out)}"
          readings.modify fun r => { r with nonQuestionMarkedOwn := r.nonQuestionMarkedOwn + 1 }
      if !prep.inFlow then
        let dis := if prep.allowDirectives then
          { prep with allowDirectives := false, documentEverStarted := true } else prep
        match scanNextToken_dispatchBlockIndicators dis c with
        | .ok (some _) =>
          if c == ':' && 0 ≤ out.currentIndent then
            let own := out.currentIndent.toNat
            let marks := markedCols out
            readings.modify fun r => { r with
              valueSlots := r.valueSlots + 1
              valueSlotOwnMarked := r.valueSlotOwnMarked + (if own ∈ marks then 1 else 0)
              valueSlotAncestors := r.valueSlotAncestors + (if marks.isEmpty then 0 else 1) }
            if own ∈ marks then
              IO.println s!"VALUE_SLOT_OWN_COLUMN_REFUTED source={repr input} step={step} own={own} marks={marks}"
          if c == '-' then
            let marks := markedCols out
            let right := marks.any (fun nv => prep.col < nv)
            let equal := prep.col ∈ marks
            let old ← readings.get
            if right && old.dashRightMarks < 4 then
              IO.println s!"DASH_UPPER_BOUND_REFUTED source={repr input} step={step} landing={prep.col} marks={marks}"
            if equal && old.dashEqualMarks < 4 then
              IO.println s!"DASH_STRICT_BOUND_REFUTED source={repr input} step={step} landing={prep.col} marks={marks}"
            readings.modify fun r => { r with
              dashLandings := r.dashLandings + 1
              dashRightMarks := r.dashRightMarks + (if right then 1 else 0)
              dashEqualMarks := r.dashEqualMarks + (if equal then 1 else 0) }
        | _ => pure ()
      walk input readings fuel (step + 1) out
    | _, .error e => throw <| IO.userError s!"accepted source scan failed: {e} in {repr input}"
    | _, _ => throw <| IO.userError s!"preprocess/scan disagreement in {repr input}"

def nest : Nat → String → String
  | 0, leaf => leaf
  | d + 1, leaf => "?\n" ++ "\n".intercalate
      ((nest d leaf).splitOn "\n" |>.map ("  " ++ ·)) ++ "\n: outer"

def main : IO Unit := do
  let readings ← IO.mkRef ({} : Readings)
  let leaves := ["plain", "  indented", "'quoted'", "\"quoted\"", "&a value", "!<tag:yaml.org,2002:str> value",
    "|-\n  block", ">-\n  folded", "? a\n: b", "?\n- b", "a:\n- b", "a:\n  - b",
    "? ? a\n  : - b\n: c", "? a\n: - b\n: c", "?\n  ? -\n- b", "?\n  ? - a\n: w",
    "[one, {two: three}]", "{one: [two, three]}"]
  for depth in [0, 1, 2, 3, 5] do
    for leaf in leaves do
      for prologue in ["", "# comment\n", "\uFEFF"] do
        for crlf in [false, true] do
          let input := prologue ++ nest depth leaf
          let input := if crlf then "\r\n".intercalate (input.splitOn "\n") else input
          if (parseYaml input).isOk then
            readings.modify fun r => { r with accepted := r.accepted + 1 }
            let initial := (ScannerState.mk' input).emit .streamStart
            let initial := if initial.peek? == some '\uFEFF' then initial.consumeBOM else initial
            walk input readings (4 * input.length + 32) 0 initial
          else
            let old ← readings.get
            if old.rejected < 4 then IO.println s!"REJECTED_SOURCE_CONTROL {repr input}"
            readings.modify fun r => { r with rejected := r.rejected + 1 }
  let r ← readings.get
  unless r.accepted > 0 && r.rootIndented > 0 && r.nonQuestionMarkedOwn > 0 && r.valueSlots > 0 && r.dashLandings > 0 do
    throw <| IO.userError "control grid did not reach all required positive/negative classes"
  unless r.valueSlotOwnMarked == 0 && r.valueSlotAncestors > 0 do
    throw <| IO.userError "proper-ancestor domain controls failed or were vacuous"
  IO.println s!"REACHABLE_CONTROL_READINGS {repr r}"
  IO.println s!"ROOT_DOMAIN_CONTROL passed={r.rootPreprocess} initialized_from_source=true"
  IO.println s!"R2_POST_VALUE_CONTROL slots={r.valueSlots} own_marked={r.valueSlotOwnMarked} with_ancestors={r.valueSlotAncestors}"
  IO.println s!"R1_DASH_CONTROL landings={r.dashLandings} marks_right={r.dashRightMarks} marks_equal={r.dashEqualMarks}"
