module

public import L4YAML.Proofs.Production.StreamAccum
public meta import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Parser.Composition
public meta import L4YAML.Parser.Composition

@[expose] public section

/-!
# Reachable same-column map-cover obstruction

Pinned source: nasa-jpl/L4YAML 64795a8db28ccfdae85082c93b6453001ae9d3e4.
Status at preparation: CANDIDATE, NOT YET COMPILED.

Existing authority: Tests/AdversarialInstantiation.lean, Priority 87,
`testNoMapLineArm`, especially its six exact entryFails, and DOCS item 435.
This isolated diagnostic narrows that experiment to the native `-` birth in
`a:\n- b`. Every recorded state comes from `mk'`, `scanNextToken_preprocess`
and `scanNextToken`; no scanner state is hand-forged.

The logic lemma has no native_decide. Only the concrete reachability/topology
fact uses native_decide, explicitly printed separately in the axiom report.
This refutes a proposed unconditional cover interface on this reached state.
It does NOT say YAML parsing is wrong or that all pending-node proofs follow
one particular constructor branch; the public parser acceptance is checked
independently below.
-/

set_option autoImplicit false

namespace ReachableCoverAudit

open L4YAML
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.IndentStackCover (FrameLevel Floor Covered)

deriving instance DecidableEq for IndentEntry

structure EntryBirth where
  before : ScannerState
  prepared : ScannerState
  after : ScannerState

def lastIsEntry (s : ScannerState) : Bool :=
  match lastRealToken? s.tokens with
  | some t => t.val == .blockEntry
  | none => false

/-- The same step-by-step driver as P87; retain only actual successful dash
births, with both sides of preprocessing visible. -/
def entryBirths : Nat → ScannerState → List EntryBirth
  | 0, _ => []
  | fuel + 1, s =>
    match scanNextToken_preprocess s with
    | .ok (some (sP, c)) =>
      match scanNextToken s with
      | .ok (some sN) =>
        let rest := entryBirths fuel sN
        if c == '-' && sP.flowLevel == 0 && lastIsEntry sN then
          { before := s, prepared := sP, after := sN } :: rest
        else rest
      | _ => []
    | _ => []

def source : String := "a:\n- b"
def initial : ScannerState := ScannerState.mk' source
def births : List EntryBirth := entryBirths 40 initial
def witnessBirth : EntryBirth :=
  births.headD { before := initial, prepared := initial, after := initial }
def witnessState : ScannerState := witnessBirth.after

def stackSnapshot (s : ScannerState) : List (Int × Bool) :=
  s.indents.toList.map fun e => (e.column, e.isSequence)

def stateSnapshot (s : ScannerState) : Nat × Nat × Int × List (Int × Bool) × Bool :=
  (s.line, s.col, s.currentIndent, stackSnapshot s, lastIsEntry s)

def birthSnapshot (b : EntryBirth) :=
  (stateSnapshot b.before, stateSnapshot b.prepared, stateSnapshot b.after)

#eval ("minimal source", source)
#eval ("native birth trace: before/prepared/after", births.map birthSnapshot)
#eval ("public parse accepts", (parseYaml source).isOk)

-- Source-derived expectations, not yet certified until this file succeeds.
#guard births.length == 1
#guard (parseYaml source).isOk
#guard witnessBirth.prepared.line == 1 && witnessBirth.prepared.col == 0
#guard witnessState.line == 1 && witnessState.col == 1
#guard lastIsEntry witnessState
#guard stackSnapshot witnessState == [(-1, false), (0, false)]
#guard stackSnapshot witnessBirth.before == stackSnapshot witnessState

-- The following observation corresponds to P87's AFTER-preprocess pause @1:2.
#guard (match scanNextToken_preprocess witnessState with
  | .ok (some (sP, c)) => sP.line == 1 && sP.col == 2 && c == 'b' &&
      stackSnapshot sP == [(-1, false), (0, false)]
  | _ => false)

/-- Separate native execution boundary: the complete physical stack, not a
hand-supplied abstract scanner state. -/
lemma reached_stack_exact : witnessState.indents =
    #[({ column := -1, isSequence := false } : IndentEntry),
      ({ column := 0, isSequence := false } : IndentEntry)] := by
  native_decide

lemma reached_top_is_mapping_zero : witnessState.indents.back? = some
    ({ column := 0, isSequence := false } : IndentEntry) := by
  rw [reached_stack_exact]
  rfl

/-- Pure native-type logic. The contradiction uses the actual physical map,
the floor bound and the strict residual-width bound; no execution axiom. -/
lemma interface_contradiction {sc : ScannerState} {n : Nat} {ks : List FrameLevel}
    (h_top : sc.indents.back? = some
      ({ column := (n : Int), isSequence := false } : IndentEntry))
    (h_lt : ∀ f ∈ ks, f.width < n) :
    ¬ (∃ lo : Nat, Floor lo n ks ∧ Covered lo ks sc) := by
  rintro ⟨lo, h_floor, h_cover⟩
  have h_mem := Array.mem_of_back? h_top
  have h_lo : (lo : Int) ≤ (n : Int) := by
    have h_bound := h_floor.1
    omega
  have h_frame : FrameLevel.map n ∈ ks := by
    simpa using h_cover _ h_mem rfl h_lo
  exact Nat.lt_irrefl n (h_lt (FrameLevel.map n) h_frame)

/-- The interface contradiction instantiated at an actually executed state
from a publicly accepted input. The logical result quantifies over ALL lists
and floors satisfying the existing field bounds, not a chosen empty list. -/
lemma reached_old_cover_impossible (ks : List FrameLevel)
    (h_lt : ∀ f ∈ ks, f.width < 0) :
    ¬ (∃ lo : Nat, Floor lo 0 ks ∧ Covered lo ks witnessState) :=
  interface_contradiction reached_top_is_mapping_zero h_lt

/-- Positive boundary control on the SAME reached state: retaining its own
map makes the intended scanner cover inhabitable at the SAME floor zero.
Only the execution fact above is native; the covering argument is structural. -/
lemma reached_retained_map_cover :
    Floor 0 0 [FrameLevel.map 0] ∧
      Covered 0 [FrameLevel.map 0] witnessState := by
  constructor
  · simp [Floor]
  · intro e h_mem _ h_lo
    have h_cases : e = ({ column := -1, isSequence := false } : IndentEntry) ∨
        e = ({ column := 0, isSequence := false } : IndentEntry) := by
      simpa [reached_stack_exact] using h_mem
    rcases h_cases with rfl | rfl
    · simp at h_lo
    · exact List.mem_cons_self

def positiveSources : List String :=
  ["a: !!seq\n- b", "a:\n- b", "a:\n- b\n- c\nd: 1",
   "k:\n- x: 1\n  y: 2", "k:\n- - a\n  - b"]

#eval positiveSources.map fun src =>
  (src, (parseYaml src).isOk,
    (entryBirths 80 (ScannerState.mk' src)).map birthSnapshot)

#print axioms reached_stack_exact
#print axioms reached_top_is_mapping_zero
#print axioms interface_contradiction
#print axioms reached_old_cover_impossible
#print axioms reached_retained_map_cover

end ReachableCoverAudit

end
