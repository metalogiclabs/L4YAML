module
public import Tests.Guards.Proofs.OwnerExplicitKeyTransport
import all Tests.Guards.Proofs.OwnerExplicitKeyTransport
public import L4YAML.Proofs.Scanner.StaleCursorFloor
public section
set_option maxHeartbeats 4000000
namespace L4YAML.Tests.Guards.OwnerExplicitKeyFreshTransport
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.StaleCursorFloor
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Tests.Guards.OwnerExplicitKeyPark
open L4YAML.Tests.Guards.OwnerExplicitKeyTransport

-- Blueprint 7.7 chain: fresh native reservations → matched-colon owner fold
-- → depth-zero scanner fold → scan_trace (the latter two remain open).
private lemma prepare_fresh_silent {s : ScannerState} {ts : Array (Positioned YamlToken)}
    {ph : Positioned YamlToken} (ht : s.tokens = (ts.push ph).push ph)
    (hp : ph.val = .placeholder) (hf : s.inFlow = false)
    (hi : s.simpleKey.possible = true → s.simpleKey.tokenIndex = ts.size) :
    SilentTokens s.tokens (scanValuePrepare s).tokens := by
  unfold scanValuePrepare
  split
  · rename_i hposs
    rw [hi hposs]
    simp only [hf, Bool.not_false, ↓reduceIte]
    split <;> intro p <;>
      simp [ht, Array.toList_setIfInBounds, Array.toList_push,
        goOut_append, goOut, tokenEvent, hp]
  · split
    · intro p; rfl
    · simp only [hf, Bool.not_false, ↓reduceIte]
      unfold pushMappingIndent
      split
      · intro p
        simp [ScannerState.emit, Array.toList_push, goOut_append, goOut, tokenEvent]
      · intro p; rfl

/-- A fresh block-context save makes the colon's retroactive writes silent,
    whether scanValueClearKey clears that reservation or leaves it live. -/
lemma scanValue_silent_after_fresh_save {s s' : ScannerState}
    (hf : s.inFlow = false) (ha : s.simpleKeyAllowed = true)
    (h : scanValue (closeStaleExplicitKey (saveSimpleKey s)) = .ok s') :
    SilentTokens (saveSimpleKey s).tokens s'.tokens := by
  let r := closeStaleExplicitKey (saveSimpleKey s)
  have ht : r.tokens = (s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
      ⟨s.currentPos, .placeholder, s.currentPos⟩ := by
    dsimp [r]
    rw [closeStaleExplicitKey_tokens]
    simp [saveSimpleKey, hf, ha]
  have hrflow : r.inFlow = false := by
    dsimp [r]
    rw [closeStaleExplicitKey_inFlow]
    unfold ScannerState.inFlow at hf ⊢
    rw [saveSimpleKey_preserves_flowLevel]
    exact hf
  have hidx : r.simpleKey.tokenIndex = s.tokens.size := by
    dsimp [r]
    rw [closeStaleExplicitKey_simpleKey]
    simp [saveSimpleKey, hf, ha]
  have hc := scanValueClearKey_preserves_tokens r
  have hcf : (scanValueClearKey r).inFlow = false := by
    unfold scanValueClearKey
    split <;> (try split) <;> (try split) <;> exact hrflow
  have hci : (scanValueClearKey r).simpleKey.possible = true →
      (scanValueClearKey r).simpleKey.tokenIndex = s.tokens.size := by
    unfold scanValueClearKey
    split <;> (try split) <;> (try split) <;> simp_all
  have hp := prepare_fresh_silent (ht := hc.trans ht) (hp := rfl) hcf hci
  change scanValue r = .ok s' at h
  unfold scanValue at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · injection h with heq; subst heq
        intro p
        dsimp only []
        rw [advance_preserves_tokens]
        simp only [ScannerState.emit, Array.toList_push, goOut_append]
        simpa [goOut, tokenEvent, hc, r] using hp p

/-- A column decrease forces the actual break branch. Reading that branch
    directly avoids the owner's native-decide line-counter dependencies. -/
lemma skip_col_drop_allowed {s s' : ScannerState}
    (h : skipToContent s = .ok s') (hf : s.inFlow = false)
    (hd : s'.col < s.col) : s'.simpleKeyAllowed = true := by
  unfold skipToContent skipToContentLoop at h
  split at h
  · contradiction
  · rename_i v hws
    have hc1 := skipToContentWs_col_ge hws
    have hc2 := skipToContentComment_col_ge v
    have hfl1 := skipToContentWs_preserves_flowLevel s v hws
    have hfl2 := skipToContentComment_preserves_flowLevel v
    dsimp only [] at h
    split at h
    · split at h
      · have hfl3 := consumeNewline_preserves_flowLevel (skipToContentComment v)
        split at h
        · exact L4YAML.Proofs.EntryBoundaryLayout.skipToContentLoop_simpleKeyAllowed_mono _ _ _ rfl h
        · rename_i hflow
          exfalso
          apply hflow
          unfold ScannerState.inFlow at hf ⊢
          rw [hfl3, hfl2, hfl1]
          simpa using hf
      · injection h with heq; subst heq; omega
    · injection h with heq; subst heq; omega

/-- A decreasing preprocessing column forces a line change, so the scanner
    arms a fresh reservation. No reachability or explicit-key register guard. -/
lemma preprocess_value_silent_of_col_drop {s p s' : ScannerState}
    (hf : s.inFlow = false)
    (hpre : scanNextToken_preprocess s = .ok (some (p, ':')))
    (hcol : p.col < s.col) (hv : scanValue p = .ok s') :
    SilentTokens s.tokens s'.tokens := by
  have hs := preprocess_silent hpre
  suffices ht : SilentTokens p.tokens s'.tokens from fun pending => (ht pending).trans (hs pending)
  unfold scanNextToken_preprocess at hpre
  simp only [bind, Except.bind, pure, Except.pure] at hpre
  split at hpre
  · contradiction
  · rename_i v hskip
    have hvf : v.inFlow = false := by
      unfold ScannerState.inFlow at hf ⊢
      rw [skipToContent_preserves_flowLevel s v hskip]
      exact hf
    have apply_fresh : ∀ st : ScannerState, st.inFlow = false →
        st.col = v.col → st.simpleKeyAllowed = v.simpleKeyAllowed →
        p = closeStaleExplicitKey (saveSimpleKey st) → SilentTokens p.tokens s'.tokens := by
      intro st hstf hstcol hsta hpeq
      have hpc : p.col = v.col := by
        rw [hpeq, closeStaleExplicitKey_col, L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col, hstcol]
      have ha : st.simpleKeyAllowed = true :=
        hsta.trans (skip_col_drop_allowed hskip hf (by omega))
      rw [hpeq] at hv ⊢
      rw [closeStaleExplicitKey_tokens]
      exact scanValue_silent_after_fresh_save hstf ha hv
    split at hpre
    · simp at hpre
    · split at hpre
      · split at hpre
        · contradiction
        · split at hpre
          · simp at hpre
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hpre
            obtain ⟨heq, _⟩ := hpre
            apply apply_fresh { unwindIndents v ↑v.col with needIndentCheck := false }
            · unfold ScannerState.inFlow at hvf ⊢
              rw [unwindIndents_preserves_flowLevel]; exact hvf
            · exact unwindIndents_col v _
            · exact L4YAML.Proofs.EntryBoundaryLayout.unwindIndents_preserves_simpleKeyAllowed v _
            · exact heq.symm
      · split at hpre
        · contradiction
        · split at hpre
          · simp at hpre
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hpre
            obtain ⟨heq, _⟩ := hpre
            exact apply_fresh v hvf rfl rfl heq.symm

/-- Matched-colon fold with transport derived from actual scanner transitions.
    Both the arbitrary PushesTrace and the cleared-key guard have been removed. -/
lemma matched_colon_owner_fold_from_transitions
    {start q after scan sp_colon sp_block : SurfPos} {n : Nat}
    {s sc_colon sc_after : ScannerState} {vc : Char} {ec eo ek : List Event}
    (hS : TSLYamlStream start s sp_block ec (eo ++ ek) [])
    (park : KeyReady start q after scan n s ec eo ek)
    (h_deeper : n < scan.col) (h_colon_col : sp_colon.col = n)
    (h_flow : sc_colon.inFlow = false)
    (hpre : scanNextToken_preprocess s = .ok (some (sc_colon, ':')))
    (hcorr_colon : ScannerSurfCorr sc_colon sp_colon)
    (hcolon : scanValue sc_colon = .ok sc_after) :
    ∃ sp_after, ScannerSurfCorr sc_after sp_after ∧
      TSLYamlStream start sc_after sp_block ec (eo ++ ek) [] ∧
      TPendingNode start false sp_block sp_after ec (eo ++ ek) [] ∧
      TPendingNode.ContentPark start sp_after vc ec (n + 1) (eo ++ ek) := by
  have hfl : s.inFlow = false := by
    unfold ScannerState.inFlow at h_flow ⊢
    rw [← L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s sc_colon ':' hpre]
    exact h_flow
  have hdrop : sc_colon.col < s.col := by
    cases park with
    | ready gram hq hc =>
      have h1 := hc.col_eq
      have h2 := hcorr_colon.col_eq
      omega
  have htrace := preprocess_value_silent_of_col_drop hfl hpre hdrop hcolon
  obtain ⟨sp_after, hcorr, hp, hc⟩ :=
    retained_key_to_owner_value_park (vc := vc) park h_deeper h_colon_col
      h_flow hpre hcorr_colon hcolon
  refine ⟨sp_after, hcorr, ⟨hS.stream, ?_⟩, hp, hc⟩
  rw [htrace [], hS.events]

#print axioms scanValue_silent_after_fresh_save
#print axioms preprocess_value_silent_of_col_drop
#print axioms matched_colon_owner_fold_from_transitions
run_meta do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``scanValue_silent_after_fresh_save, ``preprocess_value_silent_of_col_drop,
      ``matched_colon_owner_fold_from_transitions] do
    let axs ← Lean.collectAxioms n
    let rejected := axs.filter fun a => !allowed.contains a
    unless rejected.isEmpty do throwError "fresh native transport rejected {n}: {rejected}"
    Lean.logInfo m!"OWNER_FRESH_NATIVE_STANDARD_AXIOMS_ONLY {n}: {axs}"

end L4YAML.Tests.Guards.OwnerExplicitKeyFreshTransport
