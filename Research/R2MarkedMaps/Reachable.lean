import Research.R2MarkedMaps.Stages
import Research.R2JointFrames.Slots

set_option autoImplicit false
open L4YAML L4YAML.Scanner L4YAML.Proofs L4YAML.Surface
open L4YAML.Proofs.PendingKeySound L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.R2ConsumptionClosure

namespace R2JointFrames

lemma marked_next {s t : ScannerState} (ok : scanNextToken s = .ok (some t))
    (maps : MarkedMaps s) (sound : Sound s) (mono : IndentStackMono.Mono s)
    (base : SentinelBase s) (floor : PreprocessFloor s) : MarkedMaps t := by
  unfold scanNextToken at ok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at ok
  split at ok
  · cases ok
  · split at ok
    · simp at ok
    · rename_i prep c preprocess
      have pMaps := marked_preprocess preprocess maps sound.slots
      have pSound := preprocess_sound preprocess sound mono
      have pBase := preprocess_base preprocess base
      have pFloor := floor prep c preprocess
      split at ok
      · cases ok
      split at ok
      · cases ok
      split at ok
      · cases ok
      · split at ok
        · simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok
          exact marked_structural ‹_› pMaps pSound.slots
        · split at ok
          · cases ok
          split at ok
          · cases ok
          · rcases ad : prep.allowDirectives with _ | _
            <;> simp only [ad, Bool.false_eq_true, ↓reduceIte] at ok
            · generalize fi : scanNextToken_dispatchFlowIndicators prep c = result at ok
              cases result with
              | error => cases ok
              | ok option =>
                cases option with
                | some next =>
                  simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok
                  exact marked_flow fi pMaps
                | none =>
                  generalize bi : scanNextToken_dispatchBlockIndicators prep c = result at ok
                  cases result with
                  | error => cases ok
                  | ok option =>
                    cases option with
                    | some next =>
                      simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok
                      exact marked_blockDispatch bi pMaps pBase pFloor
                    | none =>
                      generalize av : scanNextToken_checkAdjacentValue prep c = result at ok
                      cases result with
                      | error => cases ok
                      | ok _ =>
                        generalize dc : scanNextToken_dispatchContent prep c = result at ok
                        cases result with
                        | error => cases ok
                        | ok next =>
                          simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok
                          exact marked_content dc pMaps
            · generalize updatedEq :
                (({ prep with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = updated at ok
              have uMaps : MarkedMaps updated := by
                rw [← updatedEq]; exact pMaps.of_eq rfl rfl
              have uBase : SentinelBase updated := by rw [← updatedEq]; exact pBase
              have uFloor : updated.inFlow = false →
                  updated.currentIndent ≤ (updated.col : Int) := by
                rw [← updatedEq]; exact pFloor
              generalize fi : scanNextToken_dispatchFlowIndicators updated c = result at ok
              cases result with
              | error => cases ok
              | ok option =>
                cases option with
                | some next =>
                  simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok
                  exact marked_flow fi uMaps
                | none =>
                  generalize bi : scanNextToken_dispatchBlockIndicators updated c = result at ok
                  cases result with
                  | error => cases ok
                  | ok option =>
                    cases option with
                    | some next =>
                      simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok
                      exact marked_blockDispatch bi uMaps uBase uFloor
                    | none =>
                      generalize av : scanNextToken_checkAdjacentValue updated c = result at ok
                      cases result with
                      | error => cases ok
                      | ok _ =>
                        generalize dc : scanNextToken_dispatchContent updated c = result at ok
                        cases result with
                        | error => cases ok
                        | ok next =>
                          simp only [Except.ok.injEq, Option.some.injEq] at ok; subst ok
                          exact marked_content dc uMaps

lemma marked_seed (input : String) : MarkedMaps ((ScannerState.mk' input).emit .streamStart) := by
  intro i l key
  cases i <;> simp [ScannerState.emit, ScannerState.mk'] at key

-- This relation follows actual successful calls. It carries no route or
-- ownership hypothesis. The BOM constructor is only the scanner's real seed.
inductive Prefix (input : String) : ScannerState → Prop
  | seed : Prefix input ((ScannerState.mk' input).emit .streamStart)
  | bom (peek : ((ScannerState.mk' input).emit .streamStart).peek? = some '\uFEFF') :
      Prefix input ((ScannerState.mk' input).emit .streamStart).consumeBOM
  | next {s t : ScannerState} (prior : Prefix input s)
      (ok : scanNextToken s = .ok (some t)) : Prefix input t

lemma Prefix.invariants {input : String} {s : ScannerState} (hp : Prefix input s) :
    MarkedMaps s ∧ Sound s ∧ IndentStackMono.Mono s ∧ SentinelBase s ∧
      ColFloor.ColFloor s := by
  induction hp with
  | seed =>
    exact ⟨marked_seed input, ColFloor.seed_sound input, IndentStackMono.mk'_mono input,
      mk'_base input, ColFloor.seed_colfloor input⟩
  | bom peek =>
    refine ⟨(marked_seed input).of_eq (PendingKeysStable.advance_preserves_pendingKeys _)
      (ScannerLoopInvariant.advance_indents _), ColFloor.seed_bom_sound input, ?_, ?_,
      ColFloor.seed_bom_colfloor input peek⟩
    · exact (IndentStackMono.mk'_mono input).of_indents_eq (ScannerLoopInvariant.advance_indents _)
    · exact (mk'_base input).of_indents_eq (ScannerLoopInvariant.advance_indents _)
  | next prior ok ih =>
    obtain ⟨maps, sound, mono, base, floor⟩ := ih
    obtain ⟨soundNext, floorNext⟩ := ColFloor.scanNextToken_sound_colfloor ok sound mono base floor
    exact ⟨marked_next ok maps sound mono base (ColFloor.preprocessFloor floor base),
      soundNext, IndentStackMono.scanNextToken_mono ok mono base,
      scanNextToken_base ok base, floorNext⟩

lemma Prefix.maps {input : String} {s : ScannerState} (hp : Prefix input s) : MarkedMaps s :=
  hp.invariants.1

lemma Prefix.entries {input : String} {s : ScannerState} {P : SurfPos → Prop} {e : SurfPos}
    (hp : Prefix input s) (context : Context s P e) : EntryValues s P e := by
  obtain ⟨maps, sound, mono, _, _⟩ := hp.invariants
  exact context.entries mono sound.slots maps

lemma Prefix.nodes {input : String} {s : ScannerState} {start slot : SurfPos} {own : Nat}
    {rest : List IndentStackCover.FrameLevel}
    (hp : Prefix input s) (payload : Slot s (SLYamlStream start) own .blockOut slot)
    (shape : levels s = IndentStackCover.FrameLevel.map own :: rest) :
    R2InvariantPayload.NodeValues s start own slot := by
  obtain ⟨maps, sound, mono, _, _⟩ := hp.invariants
  exact payload.nodes shape mono sound.slots maps

#print axioms marked_next
#print axioms Prefix.invariants
#print axioms Prefix.entries
#print axioms Prefix.nodes

end R2JointFrames
