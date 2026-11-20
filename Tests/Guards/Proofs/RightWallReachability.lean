/-
Capstone 7.7 / S3: actual scanner reachability, with no grammar certificate
in its constructors. EligibleHistory is proved, never a reachability premise.
Consumer chain: reachable_history → first/suffix event admission → directive
consumer. The paired trace-prefix equality is a separate obligation.
-/
module

public import Tests.Guards.Proofs.RightWallDirectiveStep
public import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed
public meta import L4YAML.Proofs.Serialization.TraceOf.RightWallSeed

@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.RightWallHistory

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.DirectiveRuns
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.ScannerAllowDirectives
open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML.Proofs.EntryBoundaryLayout
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.RightWallSeed

/- Native boundary probes precede the proof. These do not alter the protected
adversarial executable. They include failed scans and fuel 0/1/2 prefixes. -/
private def eventShape (s : ScannerState) : Bool :=
  !s.allowDirectives ||
    (goOut s.tokens.toList []).1.isEmpty ||
    (goOut s.tokens.toList []).1.getLast? == some .endDocument

private def probe (s : ScannerState) : Nat → Bool
  | 0 => eventShape s
  | n + 1 => eventShape s && match scanNextToken s with
    | .ok (some t) => probe t n
    | _ => true

#guard (["", "\uFEFF%YAML 1.2\n---\na", "%TAG !e! tag:x\n---\n!e!a x",
  "&a x\n...\n%YAML 1.2\n---\ny", "a: [b, {c: d}]\n...\n%YAML 1.2\n---\nz",
  "[a]\n%YAML 1.2\n---\nb", "...\n...\n%TAG !e! tag:x\n---\nx"] : List String).all
  (fun src => [0, 1, 2, 64].all (probe (scanSeed src)))

/-- Exactly the states visited by a finite prefix of the real scanner loop.
No successful-final-scan requirement hides a bad intermediate state. -/
inductive ScannerReachable (input : String) : ScannerState → Prop where
  | seed : ScannerReachable input (scanSeed input)
  | step {s t : ScannerState} : ScannerReachable input s →
      scanNextToken s = .ok (some t) → ScannerReachable input t

lemma nonemitting_of_map_eq {a b : List (Positioned YamlToken)}
    (heq : a.map Positioned.val = b.map Positioned.val)
    (hb : ∀ t ∈ b, NonEmitting t.val) : ∀ t ∈ a, NonEmitting t.val := by
  intro t ht
  have hm : t.val ∈ b.map Positioned.val := by rw [← heq]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
  obtain ⟨u, hu, hv⟩ := List.mem_map.mp hm
  simpa [hv] using hb u hu

lemma eligibleHistory_of_values {a b : List (Positioned YamlToken)}
    (heq : a.map Positioned.val = b.map Positioned.val)
    (hb : EligibleHistory b) : EligibleHistory a := by
  rcases hb with hb | ⟨pre, post, mark, hsplit, hmark, hpost⟩
  · exact Or.inl (nonemitting_of_map_eq heq hb)
  · rw [hsplit, List.map_append, List.map_cons] at heq
    obtain ⟨pre', tail, ha, hp, ht⟩ := List.map_eq_append_iff.mp heq
    obtain ⟨mark', post', htail, hm, hs⟩ := List.map_eq_cons_iff.mp ht
    exact Or.inr ⟨pre', post', mark', by rw [ha, htail], hm.trans hmark,
      nonemitting_of_map_eq hs hpost⟩

lemma history_save (s : ScannerState) (h : EligibleHistory s.tokens.toList) :
    EligibleHistory (saveSimpleKey s).tokens.toList := by
  rcases L4YAML.Proofs.StreamAccum.saveSimpleKey_tokens_shape s with heq | ⟨q, hq, heq⟩
  · simpa [heq] using h
  · rw [heq]
    simpa using eligibleHistory_append_nonemitting_list s.tokens.toList [q, q] h
      (by intro t ht
          have he : t = q := by simpa using ht
          subst t
          simp [NonEmitting, hq, tokenEvent])

lemma history_unwind (s : ScannerState) (col : Int)
    (h : EligibleHistory s.tokens.toList) :
    EligibleHistory (unwindIndents s col).tokens.toList := by
  obtain ⟨ends, ht, he⟩ := unwindIndents_tokens_append s col
  rw [ht]
  exact eligibleHistory_append_nonemitting_list _ _ h
    (by intro t hm; simp [NonEmitting, he t hm, tokenEvent])

lemma history_preprocess {s t : ScannerState} {c : Char}
    (hpre : scanNextToken_preprocess s = .ok (some (t, c)))
    (h : EligibleHistory s.tokens.toList) : EligibleHistory t.tokens.toList := by
  obtain ⟨u, skipped, hskip, hsave, hcases⟩ := preprocess_save_elim hpre
  have hs : EligibleHistory skipped.tokens.toList := by
    simpa [skipToContent_preserves_tokens s skipped hskip] using h
  have hu : EligibleHistory u.tokens.toList := by
    rcases hcases with rfl | rfl
    · exact hs
    · exact history_unwind skipped _ hs
  rw [hsave, closeStaleExplicitKey_tokens]
  exact history_save u hu

/-- The existing directive classifier suffices even without surface coupling:
the new tokens have only directive values, hence no emitted event. -/
lemma history_directive {s t : ScannerState}
    (hok : scanDirective s = .ok t) (h : EligibleHistory s.tokens.toList) :
    EligibleHistory t.tokens.toList := by
  rcases (scanDirective_fields s t hok).1 with hv | ⟨d, hv, hd⟩
  · exact eligibleHistory_of_values hv h
  · let q : Positioned YamlToken := ⟨default, d, default⟩
    have heq : t.tokens.toList.map Positioned.val =
        (s.tokens.toList ++ [q]).map Positioned.val := by simpa [vals, toks, q] using hv
    exact eligibleHistory_of_values heq
      (eligibleHistory_append_nonemitting _ q h (directive_token_nonemitting hd))

lemma history_structural {s t : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchStructural s c = .ok (some t))
    (h : s.allowDirectives = true → EligibleHistory s.tokens.toList) :
    t.allowDirectives = true → EligibleHistory t.tokens.toList := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at hok)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (intro had; have := (scanDocumentStart_fields s).2.2.1; simp_all; done)
    | exact fun _ => native_scanDocumentEnd_establishes_history _ _ (by assumption)
    | exact fun _ => history_directive (by assumption)
        (h (scanDirective_allowDirectives (by assumption)))

/-- Universal preservation for the actual successful scanner step. Content
branches are discharged by their actual flag update, not excluded from reach. -/
lemma history_scanNextToken {s t : ScannerState}
    (h : s.allowDirectives = true → EligibleHistory s.tokens.toList)
    (hok : scanNextToken s = .ok (some t)) :
    t.allowDirectives = true → EligibleHistory t.tokens.toList := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok <;> (try (simp at hok; done))
  split at hok <;> (try (simp at hok; done))
  rename_i prep c hpre
  have hp : prep.allowDirectives = true → EligibleHistory prep.tokens.toList := by
    intro had
    exact history_preprocess hpre (h ((preprocess_preserves_allowDirectives s prep c hpre).symm.trans had))
  split at hok <;> (try (simp at hok; done))
  split at hok <;> (try (simp at hok; done))
  split at hok <;> (try (simp at hok; done))
  split at hok
  · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
    exact history_structural (by assumption) hp
  · split at hok <;> (try (simp at hok; done))
    split at hok <;> (try (simp at hok; done))
    have had : (if prep.allowDirectives = true then
        { prep with allowDirectives := false, documentEverStarted := true } else prep).allowDirectives = false := by
      split
      · rfl
      · rename_i hn; simpa using hn
    split at hok <;> (try (simp at hok; done))
    split at hok
    · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
      rw [dispatchFlowIndicators_preserves_allowDirectives (by assumption), had]
      simp
    · split at hok <;> (try (simp at hok; done))
      split at hok
      · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
        rw [dispatchBlockIndicators_preserves_allowDirectives (by assumption), had]
        simp
      · split at hok <;> (try (simp at hok; done))
        split at hok <;> (try (simp at hok; done))
        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
        rw [dispatchContent_preserves_allowDirectives _ _ _ (by assumption), had]
        simp

/-- No extra source, trace, history, or route hypothesis: all real finite
scanner prefixes, even prefixes of scans that ultimately fail, are covered. -/
lemma reachable_history {input : String} {s : ScannerState}
    (hr : ScannerReachable input s) (had : s.allowDirectives = true) :
    EligibleHistory s.tokens.toList := by
  induction hr with
  | seed =>
    left
    intro t ht
    simp [NonEmitting, seed_tokens_only_streamStart input t ht, tokenEvent]
  | step hr hs ih => exact history_scanNextToken ih hs had

#print axioms L4YAML.Proofs.StreamAccum.PendingNode.virgin_tokens
#print axioms L4YAML.Proofs.StreamAccum.scanLoop_grammar_prod
#print axioms L4YAML.Proofs.Serialization.TraceOf.StreamBridge.TPendingNode.preprocess_goOut
#print axioms L4YAML.Proofs.Serialization.TraceOf.StreamBridge.TPendingNode.directive_step_source_noPending
#print axioms L4YAML.Proofs.Serialization.TraceOf.StreamBridge.TPendingNode.docEnd_step_from_pending
#print axioms history_scanNextToken
#print axioms reachable_history

end L4YAML.Proofs.Serialization.TraceOf.RightWallHistory
end Blanket
