/- Capstone 7.7 / S3: audit the exact base-origin distinction before adding
an invariant field. These are two constructions admitted by the T interface,
not two scanner-reachable histories and not a refutation of global hRoute.
The protected consumer needs a source-bound root; the old T carrier exposes
only the outer boundary, current cursor, frame kinds/tail and events. -/
module

public import L4YAML.Proofs.Serialization.TraceOf.FlowWalk
public import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
public meta import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
public meta import Lean

@[expose] public section Blanket
namespace L4YAML.Tests.Guards.RightWallFlowOrigin

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum (FrameTail)
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed

private def input : String := " [ ]\n...\n%YAML 1.2\n---\ny"

/- First validate the proposed source/cursor relation against the native
scanner. A syntax/interface construction alone does not establish reachability. -/
#guard match scanNextToken_preprocess (scanSeed input), scanNextToken (scanSeed input) with
  | .ok (some (opener, '[')), .ok (some opened) =>
    match scanNextToken_preprocess opened with
    | .ok (some (closer, ']')) =>
      opener.offset == 1 && opener.col == 1 && closer.offset == 3 && closer.col == 3
    | _ => false
  | _, _ => false
#guard match scan input with
  | .ok ts => (goOut ts.toList []).1 == [.endDocument, .beginDocument]
  | .error _ => false
#guard ([0, 1, 2] : List Nat).all (fun fuel =>
  match scanLoop (scanSeed input) fuel with | .error _ => true | .ok _ => false)

/-- The opening literal and optional separator required by the existing
base-frame constructor. This exposes the source origin as an informative
existential witness, rather than attempting to distinguish Prop proofs. -/
def EmptyBaseOrigin (root cursor : SurfPos) : Prop :=
  ∃ opened, GLit '[' root opened ∧ GOpt (SSeparate 0 .flowOut) opened cursor

def detachedRoot (rest : List Char) : SurfPos := ⟨'[' :: ']' :: rest, 2⟩
def sourceRoot (rest : List Char) : SurfPos := ⟨'[' :: ' ' :: ']' :: rest, 1⟩
def cursor (rest : List Char) : SurfPos := ⟨']' :: rest, 3⟩
def afterClose (rest : List Char) : SurfPos := ⟨rest, 4⟩

lemma detached_origin (rest : List Char) : EmptyBaseOrigin (detachedRoot rest) (cursor rest) :=
  ⟨cursor rest, GLit.mk _ 2, GOpt.none _⟩

lemma source_origin (rest : List Char) : EmptyBaseOrigin (sourceRoot rest) (cursor rest) := by
  refine ⟨⟨' ' :: ']' :: rest, 2⟩, GLit.mk _ 1, GOpt.some _ _ ?_⟩
  exact SSeparateLines.inline 0 _ _
    (SSeparateInLine.whites _ _ (GPlus.mk _ _ _ (SSWhite.space _ 2) (GStar.nil _)))

lemma distinct_origins (rest : List Char) : detachedRoot rest ≠ sourceRoot rest := by
  intro h
  have hc := congrArg SurfPos.col h
  change (2 : Nat) = 1 at hc
  omega

/-- Even with all exposed indices fixed, the current base constructor admits
both origins. This refutes uniqueness of the base-origin interface, not any
claim about actual scanner-reachable states. -/
lemma same_exposed_stack_two_origins (rest : List Char) (outer : SurfPos) :
    EmptyBaseOrigin (detachedRoot rest) (cursor rest) ∧
    EmptyBaseOrigin (sourceRoot rest) (cursor rest) ∧
    detachedRoot rest ≠ sourceRoot rest ∧
    TFlowStackB 0 1 #[true] #[false] .sep outer (cursor rest) [] := by
  obtain ⟨openedA, hOpenA, hSepA⟩ := detached_origin rest
  obtain ⟨openedB, hOpenB, hSepB⟩ := source_origin rest
  have hStackA : TFlowStackB 0 1 #[true] #[false] .sep outer (cursor rest) [] :=
    TFlowStackB.openSeqBase hOpenA hSepA
  have hStackB : TFlowStackB 0 1 #[true] #[false] .sep outer (cursor rest) [] :=
    TFlowStackB.openSeqBase hOpenB hSepB
  exact ⟨⟨openedA, hOpenA, hSepA⟩, ⟨openedB, hOpenB, hSepB⟩,
    distinct_origins rest, hStackA⟩

/-- A precise rejected interface claim: optional separation and a shared
cursor do not determine the opening source position. No reachability or
scanner-correctness conclusion is made by this refutation. -/
lemma base_origin_uniqueness_refuted (rest : List Char) :
    ¬ (∀ a b, EmptyBaseOrigin a (cursor rest) →
      EmptyBaseOrigin b (cursor rest) → a = b) := by
  intro h
  exact distinct_origins rest
    (h _ _ (detached_origin rest) (source_origin rest))

/-- Reuse the already proved close rather than implementing another flow
walker. A shared closing literal produces content at either of the two
admitted origins. A caller must additionally bind that origin to its source
continuation; this construction does not supply that missing global link. -/
lemma existing_close_keeps_the_origin_distinction (rest : List Char) :
    TFlowContent 0 .flowOut (detachedRoot rest) (afterClose rest) [] ∧
    TFlowContent 0 .flowOut (sourceRoot rest) (afterClose rest) [] := by
  have hClose : GLit ']' (cursor rest) (afterClose rest) := GLit.mk rest 3
  obtain ⟨openedA, hOpenA, hSepA⟩ := detached_origin rest
  obtain ⟨openedB, hOpenB, hSepB⟩ := source_origin rest
  constructor
  · exact (TSeqFrame.closeBase (sp_block := cursor rest) hOpenA hSepA
      (TSeqFrame.betweenEmpty (cursor rest)) (Or.inr ⟨rfl, rfl⟩) hClose).1
  · exact (TSeqFrame.closeBase (sp_block := cursor rest) hOpenB hSepB
      (TSeqFrame.betweenEmpty (cursor rest)) (Or.inr ⟨rfl, rfl⟩) hClose).1

#print axioms L4YAML.Tests.Guards.RightWallFlowOrigin.same_exposed_stack_two_origins
#print axioms L4YAML.Tests.Guards.RightWallFlowOrigin.base_origin_uniqueness_refuted
#print axioms L4YAML.Tests.Guards.RightWallFlowOrigin.existing_close_keeps_the_origin_distinction

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[
      ``L4YAML.Tests.Guards.RightWallFlowOrigin.same_exposed_stack_two_origins,
      ``L4YAML.Tests.Guards.RightWallFlowOrigin.base_origin_uniqueness_refuted,
      ``L4YAML.Tests.Guards.RightWallFlowOrigin.existing_close_keeps_the_origin_distinction] do
    let ax ← collectAxioms n
    let bad := ax.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "origin audit {n} has unapproved axioms: {bad}"
  logInfo "Origin audit: all three inspected profiles use only standard axioms"

end L4YAML.Tests.Guards.RightWallFlowOrigin
end Blanket
