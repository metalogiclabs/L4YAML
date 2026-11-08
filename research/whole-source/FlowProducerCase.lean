module

public import SourceBridge
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public meta import Lean

/-! Group 7.7, nested flow sequence constructor [137]. Reuse the actual
scanner chain and isolate the body-to-close handoff. This is a conditional
scanner result. The independent entries derivation must still supply the
body handoff, including the separation before the closing bracket. -/

@[expose] public section
namespace MathGraph.WholeSource.FlowProducerCase

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.EmitterScannability

/-- Any body implementation satisfying this local contract can be used.
The body starts after the opener and ends immediately before the close. -/
def BodyToClose (body tail : List Char) : Prop :=
  ∀ mid : ScannerState,
    ScannerSurfCorr mid ⟨body, mid.col⟩ →
    mid.flowLevel ≥ 2 →
    mid.currentIndent < 0 →
    mid.col > 0 →
    AllTokensOnLine mid mid.line →
    EndLineOnLine mid →
    StackEndLineOnLine mid mid.line →
    mid.directivesPresent = false →
    mid.flowStack.back? = some true →
    ∃ steps stop, ScanChain mid steps stop ∧
      ScannerSurfCorr stop ⟨']' :: tail, stop.col⟩ ∧
      stop.flowLevel = mid.flowLevel ∧ stop.inFlow = true ∧
      stop.currentIndent < 0 ∧ stop.col > 0 ∧
      AllTokensOnLine stop stop.line ∧ StackEndLineOnLine stop stop.line ∧
      stop.directivesPresent = false ∧ stop.flowStack.back? = some true

lemma nested_sequence_scans (s : ScannerState) (body tail : List Char)
    (hSource : ScannerSurfCorr s ⟨'[' :: body, s.col⟩)
    (hFlow : s.inFlow = true) (hDepth : s.flowLevel > 0)
    (hIndent : s.currentIndent < 0) (hColumn : s.col > 0)
    (hLine : AllTokensOnLine s s.line) (hEnd : EndLineOnLine s)
    (hDirectives : s.directivesPresent = false)
    (hPrevious : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false)
    (hBody : BodyToClose body tail) :
    ∃ steps final, ScanChain s (1 + steps + 1) final ∧
      ScannerSurfCorr final ⟨tail, final.col⟩ ∧ final.flowLevel = s.flowLevel := by
  obtain ⟨mid, hOpen, hMidSource, hMidDepth, hMidDirectives, hMidIndents, _,
    hMidCol, _, hMidLine, hMidEnd, hMidStackLine, _, _, _, _, _, hMidStack, _⟩ :=
    scanNextToken_flow_open_nested s body hSource hFlow hIndent hColumn hLine
      hEnd hDirectives hPrevious
  have hMidIndent : mid.currentIndent < 0 := by
    simpa only [ScannerState.currentIndent, hMidIndents] using hIndent
  have hMidKind : mid.flowStack.back? = some true := by simp [hMidStack]
  obtain ⟨steps, stop, hChain, hStopSource, hStopDepth, hStopFlow, hStopIndent,
    hStopCol, hStopLine, hStopStackLine, hStopDirectives, hStopKind⟩ :=
    hBody mid hMidSource (by omega) hMidIndent (by omega) hMidLine hMidEnd
      hMidStackLine (hMidDirectives.trans hDirectives) hMidKind
  obtain ⟨final, hClose, hFinalSource, hFinalDepth, _⟩ :=
    scanNextToken_flow_close_seq_nested stop tail hStopSource hStopFlow hStopIndent
      hStopCol (by omega) hStopLine hStopStackLine hStopDirectives hStopKind
  exact ⟨steps, final, ((ScanChain.single hOpen).trans hChain).trans
    (ScanChain.single hClose), hFinalSource, by omega⟩

-- Adversarial native instantiation: the same nested child can be followed
-- by a comma or used as an implicit key. Test the old slots directly.
private def prefixRewrite (input : String) : Bool := Id.run do
  let initial := (ScannerState.mk' input).emit .streamStart
  let .ok (some outer) := scanNextToken initial | return false
  let .ok (some inner) := scanNextToken outer | return false
  let .ok (some closed) := scanNextToken inner | return false
  let .ok (some next) := scanNextToken closed | return false
  return (List.range closed.tokens.size).any fun i =>
    (closed.tokens[i]?.map (·.val) == some .placeholder) &&
    (next.tokens[i]?.map (·.val) == some .key)

#guard prefixRewrite "[[]: x]"
#guard !prefixRewrite "[[], x]"
#guard (TokenParser.parseYaml "[[]: x]").isOk
#guard (TokenParser.parseYaml "[[], x]").isOk

#check MathGraph.WholeSource.SourceBridge.Obligation
#check nested_sequence_scans

open Lean Elab Command in
run_cmd do
  let axs ← collectAxioms ``nested_sequence_scans
  unless (axs.filter fun a =>
      !([ ``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a).isEmpty do
    throwError "UNQUALIFIED nested_sequence_scans: {axs}"
  logInfo m!"FLOW_PRODUCER_CASE_AXIOMS nested_sequence_scans: {axs}"

end MathGraph.WholeSource.FlowProducerCase
