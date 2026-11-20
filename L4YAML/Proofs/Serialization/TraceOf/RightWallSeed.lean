/-
Copyright (c) 2026. MathGraph bounded research experiment.
This module tests the genuine scanner seed of the proposed hRoute induction.
It does not claim that the scanner-wide transition induction is closed.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.StreamBridge

@[expose] public section Blanket

namespace L4YAML.Proofs.Serialization.TraceOf.RightWallSeed

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum (initial_stream_and_prefix)
open L4YAML.Proofs.ScannerCorrectness (consumeBOM_preserves_tokens)
open L4YAML.Proofs.Serialization.TraceOf.DocBridge (TSLYamlStream)
open L4YAML.Proofs.Serialization.TraceOf.RightWallRoute (DirectiveRoute)

/-- The exact scanner state after streamStart and optional BOM handling.
    This is the state the original source-grammar induction seeds. -/
def scanSeed (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  match s.peek? with
  | some '\uFEFF' => s.consumeBOM
  | _ => s

/-- The seed contains only the streamStart token; a BOM does not emit a token. -/
lemma seed_tokens_only_streamStart (input : String) :
    ∀ t ∈ (scanSeed input).tokens.toList, t.val = .streamStart := by
  have h0 :
      ∀ t ∈ (((ScannerState.mk' input).emit .streamStart).tokens.toList),
          t.val = .streamStart := by
    intro t ht
    simp [ScannerState.mk', ScannerState.emit] at ht
    simpa [ht]
  unfold scanSeed
  split
  · rw [consumeBOM_preserves_tokens]
    exact h0
  · exact h0

/-- True global-induction BASE CASE: the executable scanner's real seed
    carries the event-annotated empty stream and the source-grammar route.
    No hRoute premise or new axiom is admitted. -/
theorem scanner_seed_has_directive_route (input : String) :
    ∃ sp : SurfPos,
      ScannerSurfCorr (scanSeed input) sp ∧
      TSLYamlStream ⟨input.toList, 0⟩ (scanSeed input) sp [] [] [] ∧
      DirectiveRoute ⟨input.toList, 0⟩ sp [] := by
  obtain ⟨sp, _hStream, hCorr, _hCol, hPrefix⟩ :=
    initial_stream_and_prefix input
  refine ⟨sp, hCorr, ?_, Or.inl ⟨rfl, hPrefix⟩⟩
  exact TSLYamlStream.seed input.toList (scanSeed input)
    (seed_tokens_only_streamStart input)

#print axioms seed_tokens_only_streamStart
#print axioms scanner_seed_has_directive_route

end L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
end Blanket
