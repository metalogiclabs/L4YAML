module
public import Tests.Guards.Proofs.ScalarKeyProducer
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling
public section
namespace L4YAML.Tests.Guards.RootEventEOF
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.ExplicitKeyCoupling
open L4YAML.Proofs.CloseStaleExplicitKey L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.PreprocessProduction L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.StreamAccum (ContentArm NextIsSep SlotGateAt)
open L4YAML.Tests.Guards.ScalarKeyProducer

/-- Event preservation is about the trace, not token-array equality. -/
lemma goOut_push_silent (ts : Array (Positioned YamlToken)) (t : Positioned YamlToken)
    (p : List String) (hev : tokenEvent t.val = none)
    (hds : t.val ≠ .documentStart)
    (htd : ∀ h px, t.val ≠ .tagDirective h px) :
    goOut (ts.push t).toList p = goOut ts.toList p := by
  rw [Array.toList_push, goOut_append, goOut_silent t hev hds htd]
  simp

lemma emit_silent (s : ScannerState) (tok : YamlToken) (p : List String)
    (hev : tokenEvent tok = none) (hds : tok ≠ .documentStart)
    (htd : ∀ h px, tok ≠ .tagDirective h px) :
    goOut (s.emit tok).tokens.toList p = goOut s.tokens.toList p := by
  unfold ScannerState.emit
  exact goOut_push_silent _ _ p hev hds htd

lemma unwind_silent (s : ScannerState) (col : Int) (p : List String) :
    goOut (unwindIndents s col).tokens.toList p = goOut s.tokens.toList p := by
  obtain ⟨ends, htok, hend⟩ := unwindIndents_tokens_append s col
  rw [htok, goOut_append]
  have he := goOut_blockEnds ends hend [] (goOut s.tokens.toList p).2
  rw [List.append_nil] at he
  rw [he]
  simp

lemma save_silent (s : ScannerState) (p : List String) :
    goOut (saveSimpleKey s).tokens.toList p = goOut s.tokens.toList p := by
  unfold saveSimpleKey
  split
  · rfl
  · split
    · dsimp only []
      rw [goOut_push_silent _ _ p (by rfl) (by simp) (by intro h px; simp)]
      exact goOut_push_silent _ _ p (by rfl) (by simp) (by intro h px; simp)
    · rfl

lemma mapping_indent_silent (s : ScannerState) (col : Int) (p : List String) :
    goOut (pushMappingIndent s col).tokens.toList p = goOut s.tokens.toList p := by
  unfold pushMappingIndent
  split
  · exact emit_silent s .blockMappingStart p (by rfl) (by decide) (by intro h px; simp)
  · rfl

lemma key_silent {s s' : ScannerState} (h : scanKey s = .ok s') (p : List String) :
    goOut s'.tokens.toList p = goOut s.tokens.toList p := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | (change goOut ((pushMappingIndent s (s.col : Int)).emit .key).advance.tokens.toList p = _
       rw [advance_preserves_tokens, emit_silent _ .key p (by rfl) (by decide) (by intro h px; simp)]
       exact mapping_indent_silent s _ p)
    | (change goOut (s.emit .key).advance.tokens.toList p = _
       rw [advance_preserves_tokens]
       exact emit_silent s .key p (by rfl) (by decide) (by intro h px; simp))
    | (change goOut (((if !s.inFlow then pushMappingIndent s (s.col : Int) else s).emit .key).advance.tokens.toList) p = _
       rw [advance_preserves_tokens, emit_silent _ .key p (by rfl) (by decide) (by intro h px; simp)]
       split
       · exact mapping_indent_silent s _ p
       · rfl)

lemma preprocess_silent (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) (p : List String) :
    goOut s1.tokens.toList p = goOut s.tokens.toList p := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at h
  split at h
  · contradiction
  · rename_i v heq_skip
    have h_skip := skipToContent_preserves_tokens s v heq_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1, closeStaleExplicitKey_tokens, save_silent]
            change goOut (unwindIndents v v.col).tokens.toList p = _
            rw [unwind_silent, h_skip]
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1, closeStaleExplicitKey_tokens, save_silent, h_skip]

/-- The cleared explicit value cannot overwrite a reservation. A real
    implicit-key overwrite belongs to the separate stamped route. -/
lemma value_prepare_cleared_silent (s : ScannerState)
    (hc : s.simpleKey.possible = false) (p : List String) :
    goOut (scanValuePrepare s).tokens.toList p = goOut s.tokens.toList p := by
  unfold scanValuePrepare
  simp only [hc, Bool.false_eq_true, if_false]
  split
  · rfl
  · split
    · exact mapping_indent_silent s _ p
    · rfl

lemma value_cleared_silent {s s' : ScannerState}
    (h : scanValue s = .ok s')
    (hc : (scanValueClearKey s).simpleKey.possible = false) (p : List String) :
    goOut s'.tokens.toList p = goOut s.tokens.toList p := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have he := Except.ok.inj h
        subst he
        change goOut ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.tokens.toList p = _
        rw [advance_preserves_tokens,
          emit_silent _ .value p (by rfl) (by decide) (by intro h px; simp),
          value_prepare_cleared_silent _ hc,
          scanValueClearKey_preserves_tokens]

lemma scalar_dispatch_silent {s_ad s' : ScannerState} {c : Char} {sp_prep sp_a : SurfPos}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (hdepth : s_ad.flowLevel = 0) (hdisp : scanNextToken_dispatchContent s_ad c = .ok s')
    (ha : c ≠ '&') (ht : c ≠ '!') (hl : c ≠ '*') (p : List String) :
    goOut s'.tokens.toList p = goOut s_ad.tokens.toList p := by
  obtain ⟨ev, hpush, hd⟩ := accum_step_content_trace_out arm hcorr hpeek hdepth hdisp
  have he : ev = [] := by
    rcases hd with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact h
    · exact h
    · exact False.elim (ha h)
    · exact False.elim (ht h)
    · exact False.elim (hl h)
  subst ev
  simpa using hpush.goOut_at p

/-- Same initialization, including the BOM arm, as native scan. -/
@[expose] def initial (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  match s.peek? with
  | some '\uFEFF' => s.consumeBOM
  | _ => s

/-- Retain successful native scan evidence, using the same local conversion
    as the verified full_consumption_reachable proof. No exported rfl equation. -/
lemma scan_success_initial_loop (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    scanLoop (initial input) ((input.utf8ByteSize + 1) * 4) = .ok tokens := by
  exact h

lemma initial_silent (input : String) :
    goOut (initial input).tokens.toList [] = ([], []) := by
  unfold initial
  dsimp only []
  split
  · change goOut ((ScannerState.mk' input).emit .streamStart).advance.tokens.toList [] = _
    rw [advance_preserves_tokens]
    rfl
  · rfl

/-- The native key route pays the previously free root TSLYamlStream event
    premise. No assumption about token-array equality or empty events. -/
lemma root_event_from_steps_retained
    {input : String}
    {q_prep q sc prep ad k v out vp va : ScannerState} {c vc : Char}
    {sp_prep sp_a : SurfPos}
    (hinit : scanNextToken_preprocess (initial input) = .ok (some (q_prep, '?')))
    (hqtok : q.tokens = q_prep.tokens)
    (hq : scanKey q = .ok sc)
    (hpre : scanNextToken_preprocess sc = .ok (some (prep, c)))
    (had : ad = if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true } else prep)
    (hcorr : ScannerSurfCorr ad sp_prep)
    (hpeek : ad.peek? = some c)
    (arm : ContentArm ad k c sp_prep sp_a)
    (hdepth : ad.flowLevel = 0)
    (hdisp : scanNextToken_dispatchContent ad c = .ok k)
    (ha : c ≠ '&') (ht : c ≠ '!') (hl : c ≠ '*')
    (hvpre : scanNextToken_preprocess k = .ok (some (v, ':')))
    (hv : scanValue v = .ok out)
    (hvflow : v.inFlow = false) (hvpeek : v.peek? = some ':')
    (hnotstamp : out.implicitValueLine ≠ some out.line)
    (hvprep : scanNextToken_preprocess out = .ok (some (vp, vc)))
    (hvad : va = if vp.allowDirectives then
      { vp with allowDirectives := false, documentEverStarted := true } else vp) :
    TSLYamlStream ⟨input.toList, 0⟩ va ⟨input.toList, 0⟩ [] [] [] := by
  have hc : (scanValueClearKey v).simpleKey.possible = false := by
    cases he : (scanValueClearKey v).simpleKey.possible
    · rfl
    · exact False.elim (hnotstamp (scanValue_stamp_of_cleared_key hv hvflow hvpeek he))
  have hatok : ad.tokens = prep.tokens := by rw [had]; split <;> rfl
  have hvatok : va.tokens = vp.tokens := by rw [hvad]; split <;> rfl
  refine ⟨.single _ _ _ _ [] [] (.nil _) (.none _) (.nil _), ?_⟩
  rw [hvatok, preprocess_silent _ _ _ hvprep, value_cleared_silent hv hc,
    preprocess_silent _ _ _ hvpre,
    scalar_dispatch_silent arm hcorr hpeek hdepth hdisp ha ht hl,
    hatok, preprocess_silent _ _ _ hpre, key_silent hq,
    hqtok, preprocess_silent _ _ _ hinit, initial_silent]
  rfl


lemma root_event_from_steps
    {input : String}
    {q sc prep ad k v out vp va : ScannerState} {c vc : Char}
    {sp_prep sp_a : SurfPos}
    (hinit : scanNextToken_preprocess (initial input) = .ok (some (q, '?')))
    (hq : scanKey q = .ok sc)
    (hpre : scanNextToken_preprocess sc = .ok (some (prep, c)))
    (had : ad = if prep.allowDirectives then
      { prep with allowDirectives := false, documentEverStarted := true } else prep)
    (hcorr : ScannerSurfCorr ad sp_prep)
    (hpeek : ad.peek? = some c)
    (arm : ContentArm ad k c sp_prep sp_a)
    (hdepth : ad.flowLevel = 0)
    (hdisp : scanNextToken_dispatchContent ad c = .ok k)
    (ha : c ≠ '&') (ht : c ≠ '!') (hl : c ≠ '*')
    (hvpre : scanNextToken_preprocess k = .ok (some (v, ':')))
    (hv : scanValue v = .ok out)
    (hvflow : v.inFlow = false) (hvpeek : v.peek? = some ':')
    (hnotstamp : out.implicitValueLine ≠ some out.line)
    (hvprep : scanNextToken_preprocess out = .ok (some (vp, vc)))
    (hvad : va = if vp.allowDirectives then
      { vp with allowDirectives := false, documentEverStarted := true } else vp) :
    TSLYamlStream ⟨input.toList, 0⟩ va ⟨input.toList, 0⟩ [] [] [] := by
  exact root_event_from_steps_retained hinit rfl hq hpre had hcorr hpeek arm hdepth hdisp
    ha ht hl hvpre hv hvflow hvpeek hnotstamp hvprep hvad

/-- The filtered-away token is silent at every pending-handle state. -/
lemma goOut_filter_placeholders (l : List (Positioned YamlToken)) (p : List String) :
    goOut (l.filter fun t => t.val != .placeholder) p = goOut l p := by
  induction l generalizing p with
  | nil => rfl
  | cons t ts ih =>
    by_cases hv : t.val = .placeholder
    · have hb : (t.val != .placeholder) = false := by simp [hv]
      simp only [List.filter, hb]
      rw [goOut_silent t (by rw [hv]; rfl) (by rw [hv]; simp)
        (by intro h px; rw [hv]; simp)]
      exact ih p
    · have hb : (t.val != .placeholder) = true := bne_iff_ne.mpr hv
      simp only [List.filter, hb]
      change goOut ([t] ++ ts.filter (fun u => u.val != .placeholder)) p =
        goOut ([t] ++ ts) p
      rw [goOut_append, goOut_append, ih]

lemma filter_events (ts : Array (Positioned YamlToken)) :
    tokenEvents (ts.filter fun t => t.val != .placeholder) = tokenEvents ts := by
  simp only [tokenEvents_eq_goOut, Array.toList_filter, goOut_filter_placeholders]

/-- Native terminal action closes block contexts and emits streamEnd,
    neither of which alters goOut or tokenEvents. -/
lemma terminal_events (s : ScannerState) (fuel : Nat) (ts : Array (Positioned YamlToken))
    (hnext : scanNextToken s = .ok none) (hloop : scanLoop s (fuel + 1) = .ok ts) :
    tokenEvents (ts.filter fun t => t.val != .placeholder) = tokenEvents s.tokens := by
  rw [filter_events]
  simp only [scanLoop, hnext] at hloop
  split at hloop
  · contradiction
  · split at hloop
    · contradiction
    · split at hloop
      · contradiction
      · split at hloop
        · contradiction
        · have he := Except.ok.inj hloop
          rw [← he]
          simp only [tokenEvents_eq_goOut]
          rw [emit_silent _ .streamEnd [] (by rfl) (by decide) (by intro h px; simp),
            unwind_silent]

/-- EOF is generated by the real whitespace/comment scanner, not inferred
    from the presence of a final token. This adapter consumes the retained
    scalar grammar endpoint and comment gate. -/
lemma eof_from_retained_park {input : String}
    {s s_result : ScannerState} {sp_gram sp_scan : SurfPos}
    {fuel : Nat} {ts : Array (Positioned YamlToken)}
    (hcorr : ScannerSurfCorr s sp_scan)
    (hrun : GStar SSWhite sp_gram sp_scan)
    (hgate : sp_gram = sp_scan → s.col ≠ 0 →
      ¬ (CommentOk s ∧ s.peek? = some '#'))
    (hskip : skipToContent s = .ok s_result) (heof : ¬s_result.hasMore)
    (hloop : scanLoop s (fuel + 1) = .ok ts)
    (hclose : ∀ sp_end, SSLComments sp_gram sp_end →
      TLYamlStream ⟨input.toList, 0⟩ sp_end (tokenEvents s.tokens)) :
    TraceOf input (tokenEvents (ts.filter fun t => t.val != .placeholder)) := by
  obtain ⟨sp_end, hfrom, hchars, h_ok⟩ :=
    skipToContent_eof_ssl_comments s sp_scan s_result hcorr hskip heof
  have hssl := SSLCommentsFrom_at_park hcorr hrun hgate hfrom h_ok
  have hnext : scanNextToken s = .ok none := by
    have hf : s_result.hasMore = false := by
      cases h : s_result.hasMore <;> simp_all
    unfold scanNextToken scanNextToken_preprocess
    simp [bind, Except.bind, pure, Pure.pure, Except.pure, hskip, hf]
  rw [terminal_events s fuel ts hnext hloop]
  have htrace := hclose sp_end hssl
  cases sp_end with
  | mk chars col =>
    simp only [] at hchars
    subst chars
    exact ⟨col, htrace⟩

#print axioms scan_success_initial_loop
#print axioms root_event_from_steps
#print axioms filter_events
#print axioms terminal_events
#print axioms eof_from_retained_park
end L4YAML.Tests.Guards.RootEventEOF
