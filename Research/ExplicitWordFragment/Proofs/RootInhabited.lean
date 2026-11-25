module
public import Tests.Guards.Proofs.RootMatchingTrace
public meta import Tests.Guards.Proofs.RootEventEOF
public meta import L4YAML.Scanner.Scanner
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.RootInhabited
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScanStrictCoupling L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Tests.Guards.RootEventEOF L4YAML.Tests.Guards.RootMatchingTrace
set_option maxHeartbeats 2000000

/-- Extraction is total only for constructing a candidate. Every default
    branch must be ruled out by a success equation before the proof spends it. -/
def getOk {a : Type} [Inhabited a] (x : Except ScanError a) : a :=
  match x with | .ok v => v | .error _ => default

lemma getOk_eq {a : Type} [Inhabited a] {x : Except ScanError a}
    (h : x.isOk = true) : x = .ok (getOk x) := by
  cases x with
  | error e => change false = true at h; contradiction
  | ok v => rfl

def someGood {a : Type} (x : Except ScanError (Option a)) : Bool :=
  match x with | .ok (some _) => true | _ => false

def noneGood {a : Type} (x : Except ScanError (Option a)) : Bool :=
  match x with | .ok none => true | _ => false

lemma noneGood_eq {a : Type} {x : Except ScanError (Option a)}
    (h : noneGood x = true) : x = .ok none := by
  cases x with
  | error e => simp [noneGood] at h
  | ok o => cases o <;> simp_all [noneGood]

lemma unitGood_eq {x : Except ScanError Unit} (h : x.isOk = true) : x = .ok () := by
  cases x with
  | error e => change false = true at h; contradiction
  | ok u => cases u; rfl

def prePair (s : ScannerState) : ScannerState × Char :=
  match scanNextToken_preprocess s with
  | .ok (some p) => p
  | _ => default

lemma pre_eq {s : ScannerState}
    (h : someGood (scanNextToken_preprocess s) = true) :
    scanNextToken_preprocess s = .ok (some (prePair s)) := by
  unfold prePair
  cases hx : scanNextToken_preprocess s with
  | error e => simp [hx, someGood] at h
  | ok o =>
    cases o with
    | none => simp [hx, someGood] at h
    | some p => simp [hx]

def upd (s : ScannerState) : ScannerState :=
  if s.allowDirectives then {s with allowDirectives := false, documentEverStarted := true} else s

/-- Real prefix checks that all scanner dispatch paths perform. -/
def Common (s p : ScannerState) (c : Char) : Prop :=
  (scanNextToken_checkDanglingNode s p).isOk = true ∧
  (scanNextToken_checkFlowValueIndent s p).isOk = true ∧
  noneGood (scanNextToken_dispatchStructural p c) = true ∧
  (scanNextToken_checkNoPendingDirectives p).isOk = true ∧
  (scanNextToken_checkBareDocument p).isOk = true ∧
  noneGood (scanNextToken_dispatchFlowIndicators (upd p) c) = true

lemma stepBlock {s p t : ScannerState} {c : Char}
    (hp : scanNextToken_preprocess s = .ok (some (p,c)))
    (hc : Common s p c)
    (hb : scanNextToken_dispatchBlockIndicators (upd p) c = .ok (some t)) :
    scanNextToken s = .ok (some t) := by
  rcases hc with ⟨hd, hf, hs, hn, hbare, hflow⟩
  have hflow' := noneGood_eq hflow
  unfold upd at hflow' hb
  unfold scanNextToken
  simp [hp, unitGood_eq hd, unitGood_eq hf, noneGood_eq hs,
    unitGood_eq hn, unitGood_eq hbare, hflow', hb,
    bind, Except.bind, pure, Pure.pure, Except.pure]

lemma stepContent {s p t : ScannerState} {c : Char}
    (hp : scanNextToken_preprocess s = .ok (some (p,c)))
    (hc : Common s p c)
    (hb : noneGood (scanNextToken_dispatchBlockIndicators (upd p) c) = true)
    (ha : (scanNextToken_checkAdjacentValue (upd p) c).isOk = true)
    (ht : scanNextToken_dispatchContent (upd p) c = .ok t) :
    scanNextToken s = .ok (some t) := by
  rcases hc with ⟨hd, hf, hs, hn, hbare, hflow⟩
  have hflow' := noneGood_eq hflow
  have hb' := noneGood_eq hb
  have ha' := unitGood_eq ha
  unfold upd at hflow' hb' ha' ht
  unfold scanNextToken
  simp [hp, unitGood_eq hd, unitGood_eq hf, noneGood_eq hs,
    unitGood_eq hn, unitGood_eq hbare, hflow', hb', ha', ht,
    bind, Except.bind, pure, Pure.pure, Except.pure]

/-- A real token offering the slot is a constructive witness, not an assumed SlotGateAt. -/
def offerIndex (s : ScannerState) : Nat := (prevRealIdx? s.tokens s.tokens.size).getD 0
def OfferGuard (s : ScannerState) : Prop :=
  prevRealIdx? s.tokens s.tokens.size = some (offerIndex s) ∧
    s.tokens[offerIndex s]!.val.offersNodeSlot = true
lemma slot_of_guard {s : ScannerState} (h : OfferGuard s) : SlotGateAt s :=
  slotGateAt_of_offerPred_top ⟨offerIndex s, h.1, h.2⟩

def ScalarGuard (c : Char) : Prop :=
  c ≠ '&' ∧ c ≠ '*' ∧ c ≠ '!' ∧ c ≠ '|' ∧ c ≠ '>'

/-- Candidate states are obtained from actual preprocessing and dispatch;
    no fabricated ScannerState or grammar position is supplied. -/
structure Run where
  q0 : ScannerState
  qc : Char
  q : ScannerState
  sc : ScannerState
  kp : ScannerState
  kc : Char
  ka : ScannerState
  k : ScannerState
  v : ScannerState
  cc : Char
  out : ScannerState
  vp : ScannerState
  vc : Char
  va : ScannerState
  value : ScannerState
  filtered : Array (Positioned YamlToken)

def route (input : String) : Run :=
  let (q0,qc) := prePair (initial input)
  let q := upd q0
  let sc := getOk (scanKey q)
  let (kp,kc) := prePair sc
  let ka := upd kp
  let k := getOk (scanNextToken_dispatchContent ka kc)
  let (v,cc) := prePair k
  let out := getOk (scanValue v)
  let (vp,vc) := prePair out
  let va := upd vp
  let value := getOk (scanNextToken_dispatchContent va vc)
  let filtered := getOk (scanFiltered input)
  ⟨q0,qc,q,sc,kp,kc,ka,k,v,cc,out,vp,vc,va,value,filtered⟩

/-- Computable admission of the matched explicit scalar route. The actual
    successful scan is checked independently of its local dispatch candidates.
    The fragment deliberately admits a space after each indicator. -/
def Guard (input : String) (r : Run) : Prop :=
  someGood (scanNextToken_preprocess (initial input)) = true ∧
  r.qc = '?' ∧ Common (initial input) r.q0 r.qc ∧
  (isKeyCandidate r.q && flowKeyPredecessorOk r.q && flowKeyFollowerOk r.q) = true ∧
  (scanKey r.q).isOk = true ∧ r.q.inFlow = false ∧ r.q.needIndentCheck = false ∧
  r.sc.peek? = some ' ' ∧
  someGood (scanNextToken_preprocess r.sc) = true ∧ Common r.sc r.kp r.kc ∧
  noneGood (scanNextToken_dispatchBlockIndicators r.ka r.kc) = true ∧
  (scanNextToken_checkAdjacentValue r.ka r.kc).isOk = true ∧
  (scanNextToken_dispatchContent r.ka r.kc).isOk = true ∧
  r.ka.flowLevel = 0 ∧ r.ka.col ≠ 0 ∧ ScalarGuard r.kc ∧ OfferGuard r.kp ∧
  r.q.col < r.k.col ∧
  someGood (scanNextToken_preprocess r.k) = true ∧ r.cc = ':' ∧ Common r.k r.v r.cc ∧
  r.v.allowDirectives = false ∧ isValueCandidate r.v = true ∧ (scanValue r.v).isOk = true ∧
  r.v.inFlow = false ∧ r.v.needIndentCheck = false ∧
  (r.v.simpleKey.possible = true → r.v.simpleKey.pos.col = r.v.col) ∧
  r.out.peek? = some ' ' ∧
  someGood (scanNextToken_preprocess r.out) = true ∧ Common r.out r.vp r.vc ∧
  noneGood (scanNextToken_dispatchBlockIndicators r.va r.vc) = true ∧
  (scanNextToken_checkAdjacentValue r.va r.vc).isOk = true ∧
  (scanNextToken_dispatchContent r.va r.vc).isOk = true ∧
  r.va.flowLevel = 0 ∧ r.va.col ≠ 0 ∧ ScalarGuard r.vc ∧ OfferGuard r.vp ∧
  noneGood (scanNextToken r.value) = true ∧ (scanFiltered input).isOk = true ∧
  r.v.col = r.q.col ∧ r.out.implicitValueLine ≠ some r.out.line ∧
  r.q.col + 1 ≤ r.kp.col ∧ r.q.col + 1 ≤ r.vp.col

set_option maxRecDepth 4096 in
set_option maxSynthPendingDepth 256 in
instance (input : String) (r : Run) : Decidable (Guard input r) := by
  unfold Guard Common ScalarGuard OfferGuard
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- Every admitted input has an actual successful filtered output and a direct
    independent grammar trace. All former scanner-state and grammar witnesses
    are constructed inside the proof. No oracle for TraceOf occurs in Guard. -/
lemma checked_root_trace (input : String) (h : Guard input (route input)) :
    ∃ filtered, scanFiltered input = .ok filtered ∧ TraceOf input (tokenEvents filtered) := by
  let r := route input
  change Guard input r at h
  rcases h with ⟨hpreQ, hqc, hcommonQ, hkeyflag, hkeyok, hqflow, hqnic, hqspace,
    hpreK, hcommonK, hblockK, hadjK, hdispK, hkdepth, hkcol, hscalarK, hofferK, hdeep,
    hpreC, hcc, hcommonC, hallow, hvalflag, hvalok, hcolflow, hvnic, hvfresh, hvspace,
    hpreV, hcommonV, hblockV, hadjV, hdispV, hvdepth, hvcol, hscalarV, hofferV,
    hterm, hscan, hmatch, hnostamp, hkeyfloor, hvaluefloor⟩
  have hinit : scanNextToken_preprocess (initial input) = .ok (some (r.q0, r.qc)) := pre_eq hpreQ
  have hqscan : scanKey r.q = .ok r.sc := getOk_eq hkeyok
  have hprekey : scanNextToken_preprocess r.sc = .ok (some (r.kp,r.kc)) := pre_eq hpreK
  have hkd : scanNextToken_dispatchContent r.ka r.kc = .ok r.k := getOk_eq hdispK
  have hprecolon : scanNextToken_preprocess r.k = .ok (some (r.v,r.cc)) := pre_eq hpreC
  have hcolon : scanValue r.v = .ok r.out := getOk_eq hvalok
  have hprevalue : scanNextToken_preprocess r.out = .ok (some (r.vp,r.vc)) := pre_eq hpreV
  have hvd : scanNextToken_dispatchContent r.va r.vc = .ok r.value := getOk_eq hdispV
  have hfiltered : scanFiltered input = .ok r.filtered := getOk_eq hscan
  have hterminal : scanNextToken r.value = .ok none := noneGood_eq hterm
  rw [hqc] at hinit hcommonQ
  rw [hcc] at hprecolon hcommonC
  have hbQ : scanNextToken_dispatchBlockIndicators r.q '?' = .ok (some r.sc) := by
    simp [scanNextToken_dispatchBlockIndicators, hkeyflag, hqscan,
      bind, Except.bind, pure, Pure.pure, Except.pure]
  have hstepQ := stepBlock hinit hcommonQ hbQ
  have hstepK := stepContent hprekey hcommonK hblockK hadjK hkd
  have hupdate : upd r.v = r.v := by simp [upd, hallow]
  have hbC : scanNextToken_dispatchBlockIndicators (upd r.v) ':' = .ok (some r.out) := by
    rw [hupdate]
    simp [scanNextToken_dispatchBlockIndicators, hvalflag, hcolon,
      bind, Except.bind, pure, Pure.pure, Except.pure]
  have hstepC := stepBlock hprecolon hcommonC hbC
  have hstepV := stepContent hprevalue hcommonV hblockV hadjV hvd
  have hnextK : NextIsSep r.sc := by unfold NextIsSep; rw [hqspace]; decide
  have hnextV : NextIsSep r.out := by unfold NextIsSep; rw [hvspace]; decide
  obtain ⟨p0, _, _, hc0⟩ := L4YAML.Proofs.ReachableEOF.initial_prefix_corr input
  have hi : ScannerSurfCorr (initial input) p0 := hc0
  obtain ⟨psc, hcsc⟩ := scanNextToken_corr _ _ hi _ hstepQ
  obtain ⟨pkp, hckp⟩ := scanNextToken_preprocess_corr _ _ hcsc _ _ hprekey
  have hcka : ScannerSurfCorr r.ka pkp := corr_of_allowDirectives_update hckp
  have hpeekK : r.ka.peek? = some r.kc := by
    change (upd r.kp).peek? = _
    unfold upd
    have hp := preprocess_some_peek hprekey
    split <;> exact hp
  have hnotK : r.ka.col = 0 → atDocumentBoundary r.ka = false :=
    fun h => False.elim (hkcol h)
  obtain ⟨pk, armK⟩ := contentArm_of_dispatch r.ka pkp r.kc hcka hpeekK hnotK
    (by omega) hkd
  obtain ⟨pk', hck'⟩ := scanNextToken_corr _ _ hcsc _ hstepK
  have hck : ScannerSurfCorr r.k pk := by
    cases armK <;> assumption
  obtain ⟨pv, hcv⟩ := scanNextToken_preprocess_corr _ _ hck _ _ hprecolon
  obtain ⟨pout, hcout⟩ := scanNextToken_corr _ _ hck _ hstepC
  obtain ⟨pvp, hcvp⟩ := scanNextToken_preprocess_corr _ _ hcout _ _ hprevalue
  have hcva : ScannerSurfCorr r.va pvp := corr_of_allowDirectives_update hcvp
  have hpeekV : r.va.peek? = some r.vc := by
    change (upd r.vp).peek? = _
    unfold upd
    have hp := preprocess_some_peek hprevalue
    split <;> exact hp
  have hnotV : r.va.col = 0 → atDocumentBoundary r.va = false :=
    fun h => False.elim (hvcol h)
  obtain ⟨pval, armV⟩ := contentArm_of_dispatch r.va pvp r.vc hcva hpeekV hnotV
    (by omega) hvd
  have hcval : ScannerSurfCorr r.value pval := by
    cases armV <;> assumption
  have hdeeper : r.q.col < pk.col := by rw [hck.col_eq]; exact hdeep
  rcases hscalarK with ⟨ha, hs, ht, hp, hg⟩
  rcases hscalarV with ⟨hva, hvs, hvt, hvp, hvg⟩
  refine ⟨r.filtered, hfiltered, ?_⟩
  exact scalar_root_geometry_filtered_trace hinit (by rfl) hstepQ hstepK hstepC hstepV hfiltered
    hqscan hqflow hqnic hnextK (by rfl) hckp hck hprekey armK hkdepth hkd hnotK
    ha hs ht hp hg (slot_of_guard hofferK) hdeeper hcolflow hprecolon hcv hcolon
    hcout hvnic hvfresh hnextV (by rfl) hprevalue hcvp hcval armV hvdepth hvd hnotV
    (slot_of_guard hofferV) hva hvs hvt hvp hvg hterminal hmatch hnostamp hkeyfloor hvaluefloor

end L4YAML.Tests.Guards.RootInhabited
end Blanket
