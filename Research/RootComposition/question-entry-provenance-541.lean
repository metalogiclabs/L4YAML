import L4YAML.Proofs.Scanner.RegisterWitness
import L4YAML.Output.Events
import L4YAML.Output.EventsIx

open L4YAML L4YAML.Scanner L4YAML.Proofs.RegisterWitness

def r2Seed (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  match s.peek? with
  | some '\uFEFF' => s.consumeBOM
  | _ => s

def r2ExplicitAt (s : ScannerState) : Bool :=
  match scanNextToken_preprocess s with
  | .ok (some (sp, _)) =>
    let s_kc := scanValueClearKey sp
    s_kc.explicitKeyLine.isSome && !s_kc.simpleKey.possible
      && (sp.inFlow || (sp.col : Int) == s_kc.explicitKeyCol)
  | _ => false

def r2Marks (s : ScannerState) : List Nat :=
  markedColsOf s.pendingKeys s.indentColumns

partial def r2Trace (input : String) : List (Char × Nat × Nat × Bool × List Nat × List Nat × List Nat) :=
  let rec go (s : ScannerState) (fuel : Nat) (acc : List (Char × Nat × Nat × Bool × List Nat × List Nat × List Nat)) :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      match scanNextToken s with
      | .ok (some s') =>
        let next := match scanNextToken_preprocess s with
          | .ok (some (sp, c)) =>
            if c == '?' || c == ':' then
              (c, sp.line, sp.col, r2ExplicitAt s, r2Marks s, r2Marks sp, r2Marks s') :: acc
            else acc
          | _ => acc
        go s' fuel next
      | _ => acc.reverse
  go (r2Seed input) 128 []

partial def r2Slots (input : String) : List (Bool × Int × List Nat) :=
  let rec go (s : ScannerState) (fuel : Nat) (acc : List (Bool × Int × List Nat)) :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      match scanNextToken s with
      | .ok (some s') =>
        let hit := match s'.tokens.back? with
          | some t => s'.tokens.size > s.tokens.size && (match t.val with | .value => true | _ => false)
          | none => false
        go s' fuel (if hit then (r2ExplicitAt s, s'.currentIndent, r2Marks s') :: acc else acc)
      | _ => acc.reverse
  go (r2Seed input) 128 []

#guard r2Slots "? a\n: - b" == [(true, 0, [])]
#guard r2Slots "? ? a\n  : - b\n: c" == [(true, 2, [0]), (true, 0, [])]
#guard r2Slots "?\n  ? a\n  : - b\n: c" == [(true, 2, [0]), (true, 0, [])]
#guard r2Slots "? ? ? a\n    : - b\n  : c\n: d" == [(true, 4, [0, 2]), (true, 2, [0]), (true, 0, [])]
#guard r2Slots "? earth: blue\n: moon: white" == [(false, 2, [0]), (true, 0, []), (false, 2, [])]

def r2Events (input : String) : Option String × Option String :=
  ((Events.streamToEvents input).toOption, (Events.streamToEventsIx input).toOption)

def r2Witnesses : List String :=
  ["? a\n: - b", "? ? a\n  : - b\n: c", "?\n  ? a\n  : - b\n: c",
   "? ? ? a\n    : - b\n  : c\n: d", "? earth: blue\n: moon: white"]

#guard r2Witnesses.all (fun input => let e := r2Events input; e.1.isSome && e.1 == e.2)
#eval r2Witnesses.map (fun input => (input, r2Trace input, r2Slots input, r2Events input))
