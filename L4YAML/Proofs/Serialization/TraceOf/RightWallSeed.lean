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
open L4YAML.Proofs.CouplingBridge (ScannerSurfCorr)
open L4YAML.Proofs.Serialization.TraceOf
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

/-- Optional BOM consumption leaves the already emitted token array intact. -/
lemma scanSeed_preserves_tokens (input : String) :
    (scanSeed input).tokens =
      (((ScannerState.mk' input).emit .streamStart).tokens) := by
  unfold scanSeed
  dsimp only
  cases h : (((ScannerState.mk' input).emit .streamStart).peek?) with
  | none => simp [h]
  | some c =>
    by_cases hc : c = '\uFEFF'
    · subst c
      simpa [h] using (consumeBOM_preserves_tokens
        ((ScannerState.mk' input).emit .streamStart))
    · simp [h, hc]

/-- The seed contains only the streamStart token; a BOM does not emit a token. -/
lemma seed_tokens_only_streamStart (input : String) :
    ∀ t ∈ (scanSeed input).tokens.toList, t.val = .streamStart := by
  have h0 :
      ∀ t ∈ (((ScannerState.mk' input).emit .streamStart).tokens.toList),
          t.val = .streamStart := by
    intro t ht
    simp [ScannerState.mk', ScannerState.emit] at ht
    simp [ht]
  intro t ht
  rw [scanSeed_preserves_tokens] at ht
  exact h0 t ht

/-- True global-induction BASE CASE: the executable scanner's real seed
    carries the event-annotated empty stream and the source-grammar route.
    The optional BOM is covered by the source prefix, not ignored. -/
theorem scanner_seed_has_directive_route (input : String) :
    ∃ sp : SurfPos,
      ScannerSurfCorr (scanSeed input) sp ∧
      TSLYamlStream ⟨input.toList, 0⟩ (scanSeed input) sp [] [] [] ∧
      DirectiveRoute ⟨input.toList, 0⟩ sp [] := by
  obtain ⟨sp, _hStream, hCorr, _hCol, hPrefix⟩ :=
    initial_stream_and_prefix input
  have hSeed : TSLYamlStream ⟨input.toList, 0⟩ (scanSeed input)
      ⟨input.toList, 0⟩ [] [] [] :=
    TSLYamlStream.seed input.toList (scanSeed input)
      (seed_tokens_only_streamStart input)
  have hPrefixStream : TLYamlStream ⟨input.toList, 0⟩ sp [] := by
    simpa using TLYamlStream.single ⟨input.toList, 0⟩ sp sp sp [] []
      hPrefix (TOpt.none _) (TStar.nil _)
  refine ⟨sp, hCorr, ⟨hPrefixStream, ?_⟩, Or.inl ⟨rfl, hPrefix⟩⟩
  simpa using hSeed.events

#print axioms seed_tokens_only_streamStart
#print axioms scanner_seed_has_directive_route

end L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
end Blanket
