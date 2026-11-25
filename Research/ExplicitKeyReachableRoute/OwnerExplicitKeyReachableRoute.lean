module
public import Tests.Guards.Proofs.OwnerExplicitKeyValueContentStep
public import Tests.Guards.Proofs.OwnerExplicitKeyContent
import all Tests.Guards.Proofs.OwnerExplicitKeyTransport
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling
public import L4YAML.Proofs.Scanner.IndentStackBase
@[expose] public section
set_option maxHeartbeats 4000000
namespace L4YAML.Tests.Guards.OwnerExplicitKeyReachableRoute
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.Serialization.TraceOf.StreamBridge
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.StreamAccum
open L4YAML.Tests.Guards.OwnerExplicitKeyPark
open L4YAML.Tests.Guards.OwnerExplicitKeyTransport
open L4YAML.Tests.Guards.OwnerExplicitKeyValueContentStep
open L4YAML.Tests.Guards.OwnerExplicitKeyContent

/- Blueprint 7.7 dependency: actual initial scanner execution -> first
   explicit-key QuestionPark/KeyReady -> qualified native colon/value fold
   -> depth-zero induction -> scan_trace. The last two remain open.
   All indices are surface positions or actual scanner projections.
   AdversarialControls ran before this proof was attempted. -/

/-- Exactly the initial state used by `scan`, including optional BOM. -/
def nativeSeed (input : String) : ScannerState :=
  let s := (ScannerState.mk' input).emit .streamStart
  match s.peek? with | some '\uFEFF' => s.consumeBOM | _ => s

/-- Exactly the native directive reset before block/content dispatch. -/
def documentState (s : ScannerState) : ScannerState :=
  if s.allowDirectives then
    {s with allowDirectives := false, documentEverStarted := true} else s

private lemma mapping_push_silent (s : ScannerState) (col : Int) :
    SilentTokens s.tokens (pushMappingIndent s col).tokens := by
  unfold pushMappingIndent
  split
  · intro p
    simp [ScannerState.emit, Array.toList_push, goOut_append, goOut, tokenEvent]
  · intro p; rfl

private lemma scanKey_silent {s out : ScannerState}
    (h : scanKey s = .ok out) : SilentTokens s.tokens out.tokens := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with he; subst he
       intro p
       simp only [advance_preserves_tokens, ScannerState.emit, Array.toList_push,
         goOut_append]
       first
       | (simp [goOut, tokenEvent]; done)
       | simpa [goOut, tokenEvent] using mapping_push_silent s (s.col : Int) p)
    | (injection h with he; subst he
       intro p
       simp [advance_preserves_tokens, ScannerState.emit, Array.toList_push,
         goOut_append, goOut, tokenEvent])

/-- First-document map route built with `single` and its actual prefixes.
    No previously supplied enclosing route or implicit continuation. -/
private lemma first_entry_route {start land q : SurfPos} {n : Nat}
    (hprefix : GStar SLDocumentPrefix start land) (hcol : land.col = 0)
    (hind : SIndent n land q) :
    ∀ finish ev, TBlockMapEntry n q finish ev → TLYamlStream start finish ev := by
  intro finish ev entry
  apply TLYamlStream.bareRoute hprefix finish ev
  simpa using TBlockNode.blockMap 0 .blockIn n land land land finish [] ev
    (.none _) (sslComments_refl_of_col0 hcol)
    (by simpa using TBlockMapEntries.single n land q finish ev hind entry)

/-- Native initial preprocessing constructs the enclosing route, source
    correspondence, explicit-key register and next landing's slot gate.
    Only actual native preprocessing/dispatch equations are hypotheses. -/
lemma initial_question_park (input : String) {prep out : ScannerState}
    (hpre : scanNextToken_preprocess (nativeSeed input) = .ok (some (prep, '?')))
    (hdispatch : scanNextToken_dispatchBlockIndicators (documentState prep) '?' = .ok (some out)) :
    ∃ q after, QuestionPark ⟨input.toList, 0⟩ q after prep.col out [] [] ∧
      TSLYamlStream ⟨input.toList, 0⟩ out ⟨input.toList, 0⟩ [] [] [] ∧
      out.explicitKeyLine = some prep.line ∧ out.explicitKeyCol = (prep.col : Int) ∧
      (∀ p c, scanNextToken_preprocess out = .ok (some (p, c)) → SlotGateAt p) := by
  obtain ⟨sp, _, hcseed, hcolseed, hprefix⟩ := initial_stream_and_prefix input
  change ScannerSurfCorr (nativeSeed input) sp at hcseed
  have hfseed : (nativeSeed input).inFlow = false := by
    dsimp only [nativeSeed]
    split
    · unfold ScannerState.inFlow
      rw [consumeBOM_preserves_flowLevel]; rfl
    · rfl
  have hfprep : prep.inFlow = false := by
    unfold ScannerState.inFlow at hfseed ⊢
    rw [L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel _ _ _ hpre]
    exact hfseed
  have hfad : (documentState prep).inFlow = false := by
    unfold documentState; split <;> exact hfprep
  obtain ⟨land, ws, q, hssl, hlandcol, hwhite, _, hcq, hpeek⟩ :=
    preprocess_some_ssl_comments_col0 (nativeSeed input) sp prep '?' hcseed hcolseed hpre
  have heq : q = ws := hpeek.resolve_right (by rw [preprocess_some_peek hpre]; nofun)
  subst ws
  have hind : SIndent prep.col land q := by
    rcases gstar_white_sIndent_or_tab hwhite with ⟨n, hn⟩ | htab
    · have hc := SIndent_col hn
      have hq := hcq.col_eq
      have he : n = prep.col := by omega
      simpa [he] using hn
    · exact False.elim (tab_refutes_dispatch hfprep hcseed
        (L4YAML.Proofs.SurfaceSpan.sslComments_suffix hssl) hlandcol hcq hwhite htab
        hpre hdispatch)
  have hpref := ssl_comments_extend_prefixes hprefix hcolseed hssl
  have hcad : ScannerSurfCorr (documentState prep) q := corr_of_allowDirectives_update hcq
  have hnic : (documentState prep).needIndentCheck = false := by
    have hn := L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hfseed hpre
    unfold documentState; split <;> exact hn
  have hpk : (documentState prep).peek? = some '?' := by
    have hp := preprocess_some_peek hpre
    unfold documentState; split <;> exact hp
  have hcolad : (documentState prep).col = prep.col := by unfold documentState; split <;> rfl
  obtain ⟨after, hpark⟩ := question_park_from_scan
    (start := ⟨input.toList, 0⟩) (ec := []) (eo := []) hcad hpk hdispatch hfad hnic
    (by
      intro finish ev he
      have he' : TBlockMapEntry prep.col q finish ev := by simpa only [hcolad] using he
      simpa using first_entry_route hpref hlandcol hind finish ev he')
  have hscan := dispatchBlock_question_scanKey hdispatch
  have hregs := L4YAML.Proofs.ExplicitKeyCoupling.scanKey_ok_explicitKey hscan
  have hbseed : SentinelBase (nativeSeed input) := by
    dsimp only [nativeSeed]
    split
    · unfold SentinelBase ScannerState.consumeBOM
      rw [advance_indents]; rfl
    · rfl
  have hbprep := preprocess_base hpre hbseed
  have hbad : SentinelBase (documentState prep) := by
    unfold documentState; split <;> exact hbprep
  have hbout := scanKey_base hfad hscan hbad
  have hseedtrace : TSLYamlStream ⟨input.toList, 0⟩ (nativeSeed input) ⟨input.toList, 0⟩ [] [] [] := by
    apply TSLYamlStream.seed
    intro t ht
    have htokens : (nativeSeed input).tokens = #[(ScannerState.mk' input).currentPos |> fun pos =>
        (⟨pos, .streamStart, pos⟩ : Positioned YamlToken)] := by
      dsimp only [nativeSeed]
      split
      · rw [consumeBOM_preserves_tokens]; rfl
      · rfl
    rw [htokens] at ht
    change t ∈ [⟨(ScannerState.mk' input).currentPos, .streamStart,
      (ScannerState.mk' input).currentPos⟩] at ht
    have he := List.mem_singleton.mp ht
    subst t; rfl
  have htrace : TSLYamlStream ⟨input.toList, 0⟩ out ⟨input.toList, 0⟩ [] [] [] := by
    refine ⟨hseedtrace.stream, ?_⟩
    rw [scanKey_silent hscan [], show (documentState prep).tokens = prep.tokens from by
      unfold documentState; split <;> rfl]
    rw [preprocess_silent hpre [], hseedtrace.events]
  refine ⟨q, after, ?_, htrace, ?_, ?_, ?_⟩
  · simpa [hcolad] using hpark
  · have hl : (documentState prep).line = prep.line := by unfold documentState; split <;> rfl
    simpa only [hl] using hregs.1
  · simpa [hcolad] using hregs.2
  · intro p c hp
    exact slotGateAt_of_offerPred (scanKey_offerPred hscan) hbout hp

private lemma question_dispatch_of_next {s prep out : ScannerState}
    (hpre : scanNextToken_preprocess s = .ok (some (prep, '?')))
    (hf : prep.inFlow = false) (hcan : isKeyCandidate (documentState prep) = true)
    (hnext : scanNextToken s = .ok (some out)) :
    scanNextToken_dispatchBlockIndicators (documentState prep) '?' = .ok (some out) := by
  have hp := preprocess_some_peek hpre
  have hp0 : prep.peekAt? 0 = some '?' := by
    simpa [ScannerState.peekAt?, ScannerState.peekAt?Loop, ScannerState.peek?] using hp
  have hds : atDocumentStart prep = false := by simp [atDocumentStart, hp0]
  have hde : atDocumentEnd prep = false := by simp [atDocumentEnd, hp0]
  have hs : scanNextToken_dispatchStructural prep '?' = .ok none := by
    simp [scanNextToken_dispatchStructural, hf, hds, hde, pure, Except.pure]
  have hfa : (documentState prep).inFlow = false := by unfold documentState; split <;> exact hf
  have hfi : scanNextToken_dispatchFlowIndicators (documentState prep) '?' = .ok none := by
    simp [scanNextToken_dispatchFlowIndicators, scanNextToken_checkFlowAdjacency, hfa,
      pure, Except.pure, bind, Except.bind]
  have hb : scanNextToken_dispatchBlockIndicators (documentState prep) '?' =
      (do let t ← scanKey (documentState prep); pure (some t)) := by
    simp [scanNextToken_dispatchBlockIndicators, hcan, flowKeyPredecessorOk,
      flowKeyFollowerOk, hfa, pure, Except.pure, bind, Except.bind]
  simp only [scanNextToken, hpre, bind, Except.bind, pure, Except.pure] at hnext
  cases hdn : scanNextToken_checkDanglingNode s prep with
  | error e => simp [hdn] at hnext
  | ok u =>
    cases u
    simp only [hdn] at hnext
    cases hfv : scanNextToken_checkFlowValueIndent s prep with
    | error e => simp [hfv] at hnext
    | ok u =>
      cases u
      simp only [hfv, hs] at hnext
      cases hnd : scanNextToken_checkNoPendingDirectives prep with
      | error e => simp [hnd] at hnext
      | ok u =>
        cases u
        simp only [hnd] at hnext
        cases hbd : scanNextToken_checkBareDocument prep with
        | error e => simp [hbd] at hnext
        | ok u =>
          cases u
          simp only [hbd] at hnext
          change (do
            match ← scanNextToken_dispatchFlowIndicators (documentState prep) '?' with
            | some t => pure (some t)
            | none =>
              match ← scanNextToken_dispatchBlockIndicators (documentState prep) '?' with
              | some t => pure (some t)
              | none => do
                scanNextToken_checkAdjacentValue (documentState prep) '?'
                let t ← scanNextToken_dispatchContent (documentState prep) '?'
                pure (some t)) = .ok (some out) at hnext
          rw [hfi, hb] at hnext
          cases hk : scanKey (documentState prep) with
          | error e => simp [hk, bind, Except.bind] at hnext
          | ok t =>
            simp [hk, bind, Except.bind, pure, Except.pure] at hnext
            subst out
            rw [hb, hk]; rfl

/-- The first question park now follows from a successful COMPLETE native
    scanner call and the native key-candidate branch. No independent equation
    about its returned block-dispatch state is supplied. -/
lemma initial_question_from_next (input : String) {prep out : ScannerState}
    (hpre : scanNextToken_preprocess (nativeSeed input) = .ok (some (prep, '?')))
    (hcan : isKeyCandidate (documentState prep) = true)
    (hnext : scanNextToken (nativeSeed input) = .ok (some out)) :
    ∃ q after, QuestionPark ⟨input.toList, 0⟩ q after prep.col out [] [] ∧
      TSLYamlStream ⟨input.toList, 0⟩ out ⟨input.toList, 0⟩ [] [] [] ∧
      out.explicitKeyLine = some prep.line ∧ out.explicitKeyCol = (prep.col : Int) ∧
      (∀ p c, scanNextToken_preprocess out = .ok (some (p, c)) → SlotGateAt p) := by
  have hfseed : (nativeSeed input).inFlow = false := by
    dsimp only [nativeSeed]
    split
    · unfold ScannerState.inFlow; rw [consumeBOM_preserves_flowLevel]; rfl
    · rfl
  have hfprep : prep.inFlow = false := by
    unfold ScannerState.inFlow at hfseed ⊢
    rw [L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel _ _ _ hpre]
    exact hfseed
  exact initial_question_park input hpre (question_dispatch_of_next hpre hfprep hcan hnext)

/-- The first actual key-content dispatch inherits the derived route and
    native offer's slot gate. Scanner/surface correspondence, ContentArm,
    depth and the incoming event coupling are all produced here. Properties
    remain held for the next key step; dedent remains an explicit outcome. -/
lemma initial_key_progress (input : String)
    {qprep question kprep key : ScannerState} {c : Char}
    (hqpre : scanNextToken_preprocess (nativeSeed input) = .ok (some (qprep, '?')))
    (hqcan : isKeyCandidate (documentState qprep) = true)
    (hqnext : scanNextToken (nativeSeed input) = .ok (some question))
    (hkpre : scanNextToken_preprocess question = .ok (some (kprep, c)))
    (hkdispatch : scanNextToken_dispatchContent (documentState kprep) c = .ok key)
    (hnotdoc : (documentState kprep).col = 0 → atDocumentBoundary (documentState kprep) = false) :
    ∃ q after sp_prep sp_key,
      ScannerSurfCorr kprep sp_prep ∧ ScannerSurfCorr key sp_key ∧
      ((∃ ek, TSLYamlStream ⟨input.toList, 0⟩ key ⟨input.toList, 0⟩ [] ek [] ∧
        KeyProgress ⟨input.toList, 0⟩ q after sp_key qprep.col key [] [] ek) ∨
        L4YAML.Proofs.FlowIndexLift.DedentLanding (qprep.col + 1) after sp_prep) := by
  obtain ⟨q, after, park, hs, _, _, hslot⟩ :=
    initial_question_from_next input hqpre hqcan hqnext
  obtain ⟨sp_prep, hcp⟩ := L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr
    question after park.corr kprep c hkpre
  have hca : ScannerSurfCorr (documentState kprep) sp_prep := corr_of_allowDirectives_update hcp
  have hpk : (documentState kprep).peek? = some c := by
    have hp := preprocess_some_peek hkpre
    unfold documentState; split <;> exact hp
  have hzero : question.flowLevel = 0 := by
    simpa [ScannerState.inFlow] using park.noflow
  have hdepth : (documentState kprep).flowLevel = 0 := by
    have hf := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel _ _ _ hkpre
    unfold documentState
    split <;> simpa [hf] using hzero
  obtain ⟨sp_key, arm⟩ := contentArm_of_dispatch (documentState kprep) sp_prep c hca hpk
    hnotdoc (by intro hp; omega) hkdispatch
  have hck : ScannerSurfCorr key sp_key := by cases arm <;> assumption
  have hsad : TSLYamlStream ⟨input.toList, 0⟩ (documentState kprep)
      ⟨input.toList, 0⟩ [] [] [] := by
    refine ⟨hs.stream, ?_⟩
    have ht : (documentState kprep).tokens = kprep.tokens := by unfold documentState; split <;> rfl
    rw [ht, preprocess_silent hkpre [], hs.events]
  refine ⟨q, after, sp_prep, sp_key, hcp, hck, ?_⟩
  simpa only [List.nil_append] using explicit_key_content_step hsad park rfl hcp hck hkpre
    arm hdepth hkdispatch hnotdoc (hslot kprep c hkpre)

/-- Plain/quoted first keys reach `KeyReady` directly. This is the incoming
    park the already qualified matched-colon consumer previously assumed. -/
lemma initial_scalar_key_ready (input : String)
    {qprep question kprep key : ScannerState} {c : Char}
    (hqpre : scanNextToken_preprocess (nativeSeed input) = .ok (some (qprep, '?')))
    (hqcan : isKeyCandidate (documentState qprep) = true)
    (hqnext : scanNextToken (nativeSeed input) = .ok (some question))
    (hkpre : scanNextToken_preprocess question = .ok (some (kprep, c)))
    (hkdispatch : scanNextToken_dispatchContent (documentState kprep) c = .ok key)
    (hnotdoc : (documentState kprep).col = 0 → atDocumentBoundary (documentState kprep) = false)
    (hamp : c ≠ '&') (hstar : c ≠ '*') (hbang : c ≠ '!')
    (hpipe : c ≠ '|') (hgt : c ≠ '>') :
    ∃ q after sp_prep sp_key,
      ScannerSurfCorr kprep sp_prep ∧ ScannerSurfCorr key sp_key ∧
      ((TSLYamlStream ⟨input.toList, 0⟩ key ⟨input.toList, 0⟩ [] [] [] ∧
        KeyReady ⟨input.toList, 0⟩ q after sp_key qprep.col key [] [] []) ∨
        L4YAML.Proofs.FlowIndexLift.DedentLanding (qprep.col + 1) after sp_prep) := by
  obtain ⟨q, after, park, hs, _, _, hslot⟩ :=
    initial_question_from_next input hqpre hqcan hqnext
  obtain ⟨sp_prep, hcp⟩ := L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr
    question after park.corr kprep c hkpre
  have hca : ScannerSurfCorr (documentState kprep) sp_prep := corr_of_allowDirectives_update hcp
  have hpk : (documentState kprep).peek? = some c := by
    have hp := preprocess_some_peek hkpre
    unfold documentState; split <;> exact hp
  have hzero : question.flowLevel = 0 := by simpa [ScannerState.inFlow] using park.noflow
  have hdepth : (documentState kprep).flowLevel = 0 := by
    have hf := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel _ _ _ hkpre
    unfold documentState
    split <;> simpa [hf] using hzero
  obtain ⟨sp_key, arm⟩ := contentArm_of_dispatch (documentState kprep) sp_prep c hca hpk
    hnotdoc (by intro hp; omega) hkdispatch
  have hck : ScannerSurfCorr key sp_key := by cases arm <;> assumption
  have hsad : TSLYamlStream ⟨input.toList, 0⟩ (documentState kprep)
      ⟨input.toList, 0⟩ [] [] [] := by
    refine ⟨hs.stream, ?_⟩
    have ht : (documentState kprep).tokens = kprep.tokens := by unfold documentState; split <;> rfl
    rw [ht, preprocess_silent hkpre [], hs.events]
  refine ⟨q, after, sp_prep, sp_key, hcp, hck, ?_⟩
  exact explicit_scalar_content_step hsad park rfl hcp hck hkpre arm hdepth hkdispatch
    hnotdoc hamp hstar hbang hpipe hgt (hslot kprep c hkpre)

/-- The first plain/quoted explicit key reaches the qualified owner value
    park from native initialization. No incoming grammar route, `KeyReady`,
    stream coupling, source correspondence, depth or slot gate is assumed.
    Matching/deeper columns and the actual native branch equations remain.
    The next value-content landing also receives its native slot gate. -/
lemma initial_scalar_matched_colon (input : String)
    {qprep question kprep key colon out : ScannerState} {c vc : Char}
    (hqpre : scanNextToken_preprocess (nativeSeed input) = .ok (some (qprep, '?')))
    (hqcan : isKeyCandidate (documentState qprep) = true)
    (hqnext : scanNextToken (nativeSeed input) = .ok (some question))
    (hkpre : scanNextToken_preprocess question = .ok (some (kprep, c)))
    (hkdispatch : scanNextToken_dispatchContent (documentState kprep) c = .ok key)
    (hnotdoc : (documentState kprep).col = 0 → atDocumentBoundary (documentState kprep) = false)
    (hamp : c ≠ '&') (hstar : c ≠ '*') (hbang : c ≠ '!')
    (hpipe : c ≠ '|') (hgt : c ≠ '>')
    (hcpre : scanNextToken_preprocess key = .ok (some (colon, ':')))
    (hcdispatch : scanNextToken_dispatchBlockIndicators colon ':' = .ok (some out))
    (hmatch : colon.col = qprep.col) (hdeeper : qprep.col < key.col) :
    ∃ after sp_prep,
      L4YAML.Proofs.FlowIndexLift.DedentLanding (qprep.col + 1) after sp_prep ∨
      ∃ sp_after, ScannerSurfCorr out sp_after ∧
        TSLYamlStream ⟨input.toList, 0⟩ out ⟨input.toList, 0⟩ [] [] [] ∧
        TPendingNode ⟨input.toList, 0⟩ false ⟨input.toList, 0⟩ sp_after [] [] [] ∧
        TPendingNode.ContentPark ⟨input.toList, 0⟩ sp_after vc [] (qprep.col + 1) [] ∧
        IndentFloor out (qprep.col + 1) ∧ sp_after.col = qprep.col + 1 ∧ NextIsSep out ∧
        out.inFlow = false ∧
        (∀ p cc, scanNextToken_preprocess out = .ok (some (p, cc)) → SlotGateAt p) := by
  obtain ⟨q, after, sp_prep, sp_key, _, hck, hr⟩ := initial_scalar_key_ready input
    hqpre hqcan hqnext hkpre hkdispatch hnotdoc hamp hstar hbang hpipe hgt
  refine ⟨after, sp_prep, ?_⟩
  rcases hr with ⟨hs, ready⟩ | hded
  · right
    obtain ⟨_, _, park, _, _, _, _⟩ := initial_question_from_next input hqpre hqcan hqnext
    have hzq : question.flowLevel = 0 := by simpa [ScannerState.inFlow] using park.noflow
    have hzkp : (documentState kprep).flowLevel = 0 := by
      have hf := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel _ _ _ hkpre
      unfold documentState
      split <;> simpa [hf] using hzq
    have hzk : key.flowLevel = 0 :=
      (dispatchContent_preserves_flowLevel _ _ _ hkdispatch).trans hzkp
    have hfc : colon.inFlow = false := by
      unfold ScannerState.inFlow
      rw [L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel _ _ _ hcpre, hzk]
      rfl
    obtain ⟨sp_colon, hcc⟩ := L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr
      key sp_key hck colon ':' hcpre
    have hm : sp_colon.col = qprep.col := hcc.col_eq.trans hmatch
    have hd : qprep.col < sp_key.col := by rw [hck.col_eq]; exact hdeeper
    obtain ⟨sp_after, hca, hsa, hpa, hpark, hfloor, hcol, hnext⟩ :=
      matched_colon_owner_content_ready (vc := vc) hs ready hd hm hfc hcpre hcc hcdispatch
    have hbseed : SentinelBase (nativeSeed input) := by
      dsimp only [nativeSeed]
      split
      · unfold SentinelBase ScannerState.consumeBOM; rw [advance_indents]; rfl
      · rfl
    have hbq := scanNextToken_base hqnext hbseed
    have hbkp := preprocess_base hkpre hbq
    have hbkad : SentinelBase (documentState kprep) := by
      unfold documentState; split <;> exact hbkp
    have hbk := dispatchContent_base hkdispatch hbkad
    have hbc := preprocess_base hcpre hbk
    have hbo := dispatchBlockIndicators_base hcdispatch hbc
    have hfo : out.inFlow = false := by
      unfold ScannerState.inFlow at hfc ⊢
      rw [scanValue_preserves_flowLevel colon out (dispatchBlock_colon_scanValue hcdispatch)]
      exact hfc
    refine ⟨sp_after, hca, ?_, ?_, ?_, hfloor, hcol, hnext, hfo, ?_⟩
    · simpa only [List.nil_append] using hsa
    · simpa only [List.nil_append] using hpa
    · simpa only [List.nil_append] using hpark
    · intro p cc hp
      exact slotGateAt_of_offerPred (dispatchBlock_colon_offerPred hcdispatch) hbo hp
  · exact Or.inl hded

/-- Consume the actual owner's value-content fold from the native first
    question, scalar key and matched colon. Every grammar route and both
    slot gates are produced by the scanner path above. This is a finite
    first-document fragment, not the global scanner-loop induction. -/
lemma initial_scalar_then_owner_value (input : String)
    {qprep question kprep key colon out vprep value : ScannerState} {c vc : Char}
    (hqpre : scanNextToken_preprocess (nativeSeed input) = .ok (some (qprep, '?')))
    (hqcan : isKeyCandidate (documentState qprep) = true)
    (hqnext : scanNextToken (nativeSeed input) = .ok (some question))
    (hkpre : scanNextToken_preprocess question = .ok (some (kprep, c)))
    (hkdispatch : scanNextToken_dispatchContent (documentState kprep) c = .ok key)
    (hnotdoc : (documentState kprep).col = 0 → atDocumentBoundary (documentState kprep) = false)
    (hamp : c ≠ '&') (hstar : c ≠ '*') (hbang : c ≠ '!')
    (hpipe : c ≠ '|') (hgt : c ≠ '>')
    (hcpre : scanNextToken_preprocess key = .ok (some (colon, ':')))
    (hcdispatch : scanNextToken_dispatchBlockIndicators colon ':' = .ok (some out))
    (hmatch : colon.col = qprep.col) (hdeeper : qprep.col < key.col)
    (hvpre : scanNextToken_preprocess out = .ok (some (vprep, vc)))
    (hvdispatch : scanNextToken_dispatchContent (documentState vprep) vc = .ok value)
    (hvnotdoc : (documentState vprep).col = 0 → atDocumentBoundary (documentState vprep) = false) :
    (∃ after sp_prep,
      L4YAML.Proofs.FlowIndexLift.DedentLanding (qprep.col + 1) after sp_prep) ∨
    ∃ sp_after sp_value sp_result,
      ScannerSurfCorr out sp_after ∧ ScannerSurfCorr vprep sp_value ∧
      ScannerSurfCorr value sp_result ∧
      ((∃ ev, TSLYamlStream ⟨input.toList, 0⟩ value ⟨input.toList, 0⟩ [] ev [] ∧
        TPendingNode ⟨input.toList, 0⟩ false ⟨input.toList, 0⟩ sp_result [] ev []) ∨
        L4YAML.Proofs.FlowIndexLift.DedentLanding (qprep.col + 1) sp_after sp_value) := by
  obtain ⟨after, sp_prep, hr⟩ := initial_scalar_matched_colon (vc := vc) input hqpre hqcan
    hqnext hkpre hkdispatch hnotdoc hamp hstar hbang hpipe hgt hcpre hcdispatch hmatch hdeeper
  rcases hr with hded | ⟨sp_after, hca, hs, _, park, hfloor, hcol, hnext, hnf, hslot⟩
  · exact Or.inl ⟨after, sp_prep, hded⟩
  · right
    obtain ⟨sp_value, hcv⟩ := L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr
      out sp_after hca vprep vc hvpre
    have hcad : ScannerSurfCorr (documentState vprep) sp_value := corr_of_allowDirectives_update hcv
    have hpk : (documentState vprep).peek? = some vc := by
      have hp := preprocess_some_peek hvpre
      unfold documentState; split <;> exact hp
    have hzero : out.flowLevel = 0 := by simpa [ScannerState.inFlow] using hnf
    have hdepth : (documentState vprep).flowLevel = 0 := by
      have hf := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel _ _ _ hvpre
      unfold documentState
      split <;> simpa [hf] using hzero
    obtain ⟨sp_result, arm⟩ := contentArm_of_dispatch (documentState vprep) sp_value vc
      hcad hpk hvnotdoc (by intro hp; omega) hvdispatch
    have hcr : ScannerSurfCorr value sp_result := by cases arm <;> assumption
    have hsad : TSLYamlStream ⟨input.toList, 0⟩ (documentState vprep)
        ⟨input.toList, 0⟩ [] [] [] := by
      refine ⟨hs.stream, ?_⟩
      have ht : (documentState vprep).tokens = vprep.tokens := by unfold documentState; split <;> rfl
      rw [ht, preprocess_silent hvpre [], hs.events]
    refine ⟨sp_after, sp_value, sp_result, hca, hcv, hcr, ?_⟩
    simpa only [List.nil_append] using TPendingNode.content_step_park hsad park rfl hfloor
      (by omega) (by omega) hnext hca hcv hcr hvpre arm hdepth hvdispatch hvnotdoc
      (hslot vprep vc hvpre)

#print axioms initial_question_park
#print axioms initial_question_from_next
#print axioms initial_key_progress
#print axioms initial_scalar_key_ready
#print axioms initial_scalar_matched_colon
#print axioms initial_scalar_then_owner_value
run_meta do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``initial_question_park, ``initial_question_from_next] do
    let actual ← Lean.collectAxioms n
    unless actual.all allowed.contains do
      throwError "native question producer gained nonstandard axioms: {n} {actual}"
  let owner ← Lean.collectAxioms ``TPendingNode.content_step_park
  for n in [``initial_key_progress, ``initial_scalar_key_ready, ``initial_scalar_matched_colon,
      ``initial_scalar_then_owner_value] do
    let actual ← Lean.collectAxioms n
    unless actual.all owner.contains do
      throwError "native key producer exceeds owner's content axiom closure: {n} {actual}"
    let native := actual.filter fun a => !allowed.contains a
    Lean.logInfo m!"OWNER_INITIAL_KEY_NATIVE_LEAVES {n} {native.size}"
  Lean.logInfo "OWNER_REACHABLE_QUESTION_STANDARD_ONLY"
end L4YAML.Tests.Guards.OwnerExplicitKeyReachableRoute
