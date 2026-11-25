module
public import Tests.Guards.Proofs.ExplicitWordExecution
public import Tests.Guards.Proofs.ExplicitWordParser
import all L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ExplicitWordAssurance
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.TokenEvents L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Tests.Guards.ExplicitWordFragment
open L4YAML.Tests.Guards.ExplicitWordExecution
open L4YAML.Tests.Guards.RootInhabited
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

lemma owner_initial (k v : List Char) (hk : ∀ c ∈ k, Letter c) (hv : ∀ c ∈ v, Letter c) :
 L4YAML.Tests.Guards.RootEventEOF.initial (source k v) = initial k v := by
 unfold L4YAML.Tests.Guards.RootEventEOF.initial
 change (match (initial k v).peek? with
  | some '\uFEFF' => (initial k v).consumeBOM | _ => initial k v) = _
 rw [initial_peek k v hk hv]
 rfl

def run (k v : List Char) (c d : Char) : Run :=
 ⟨qpre k v,'?',qstart k v,qout k v,kpre k v,c,kpre k v,kout k v,
   cpre k v,':',cout k v,vpre k v,d,vpre k v,vout k v,filteredTokens k v⟩

lemma route_eq (c d : Char) (ks vs : List Char)
 (hk : ∀ x ∈ c::ks, Letter x) (hv : ∀ x ∈ d::vs, Letter x) :
 route (source (c::ks) (d::vs)) = run (c::ks) (d::vs) c d := by
 have hkc := hk c (by simp)
 have hvc := hv d (by simp)
 have hkd := (letter_dispatch (kpre (c::ks) (d::vs)) c hkc).trans (key_scan _ _ hk)
 have hvd := (letter_dispatch (vpre (c::ks) (d::vs)) d hvc).trans (value_scan _ _ hk hv)
 simp [route,owner_initial _ _ hk hv,prePair,getOk,
  initial_preprocess _ _ hk hv,upd_q,question_scan _ _ hk hv,
  key_preprocess c ks (d::vs) hk hv,upd_k,hkd,
  colon_preprocess _ _ hk hv,colon_scan _ _ hk hv,
  value_preprocess (c::ks) d vs hk hv,upd_v,hvd,scan_filtered c d ks vs hk hv,run]

lemma source_guard (c d : Char) (ks vs : List Char)
 (hk : ∀ x ∈ c::ks, Letter x) (hv : ∀ x ∈ d::vs, Letter x) :
 Guard (source (c::ks) (d::vs)) (route (source (c::ks) (d::vs))) := by
 rw [route_eq c d ks vs hk hv]
 have hkc := hk c (by simp)
 have hvc := hv d (by simp)
 have hkb := letter_block (kpre (c::ks) (d::vs)) c hkc
 have hvb := letter_block (vpre (c::ks) (d::vs)) d hvc
 have hkd := (letter_dispatch (kpre (c::ks) (d::vs)) c hkc).trans (key_scan _ _ hk)
 have hvd := (letter_dispatch (vpre (c::ks) (d::vs)) d hvc).trans (value_scan _ _ hk hv)
 have h1 := source_one (c::ks) (d::vs)
 have h4 := source_space (c::ks) (d::vs) hk
 have hs := source_size (c::ks) (d::vs) hk hv
 have hm1 : 1<5+(c::ks).length+(d::vs).length := by omega
 have hm4 : 4+(c::ks).length<5+(c::ks).length+(d::vs).length := by omega
 simp only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hm1 hm4 h4 hs
 simp only [Guard,run,owner_initial _ _ hk hv,
  initial_preprocess _ _ hk hv,common_question _ _ hk hv,question_flag _ _ hk hv,question_scan _ _ hk hv,
  key_preprocess c ks (d::vs) hk hv,common_key _ _ _ hkc,hkb.1,hkb.2.1,hkb.2.2,hkd,
  colon_preprocess _ _ hk hv,common_colon _ _ hk hv,colon_flag _ _ hk hv,colon_scan _ _ hk hv,
  value_preprocess (c::ks) d vs hk hv,common_value _ _ _ hvc,hvb.1,hvb.2.1,hvb.2.2,hvd,
  (value_eof _ _ hk hv).2,scan_filtered c d ks vs hk hv,someGood,noneGood,Except.isOk,Except.toBool]
 simp [qpre,qstart,qout,kpre,kout,cpre,cout,vpre,vout,initial,afterWord,shift,
  ScannerState.mk',ScannerState.emit,ScannerState.emitAt,ScannerState.currentPos,
  ScannerState.inFlow,ScannerState.peek?,OfferGuard,offerIndex,prevRealIdx?,YamlToken.offersNodeSlot,
  pos,ExplicitWordExecution.tok,hs,h1,h4,hm1,hm4,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

/-- Blueprint 7.7 fragment: no supplied scanner success, state provenance,
    pending-node route, slot, event transport, grammar or EOF assumption. -/
lemma word_fragment_trace (k v : List Char) (hk : Word k) (hv : Word v) :
 ∃ filtered, scanFiltered (source k v) = .ok filtered ∧
  TraceOf (source k v) (tokenEvents filtered) := by
 cases k with
 | nil => exact False.elim (hk.1 rfl)
 | cons c ks =>
  cases v with
  | nil => exact False.elim (hv.1 rfl)
  | cons d vs => exact checked_root_trace _ (source_guard c d ks vs hk.2 hv.2)


lemma word_events (k v : List Char) : tokenEvents (expectedTokens k v) = [] := by
 simp [tokenEvents,go,tokenEvent,expectedTokens,ExplicitWordExecution.tok]

/-- One source-defined fragment through the real scanner fold, exact token
    payloads, raw parser/composition, owner grammar trace, and actual EOF. -/
lemma word_fragment_assurance (k v : List Char) (hk : Word k) (hv : Word v) :
 scanFiltered (source k v) = .ok (expectedTokens k v) ∧
 L4YAML.TokenParser.parseYamlSingle (source k v) = .ok (ExplicitWordParser.expected k v) ∧
 tokenEvents (expectedTokens k v) = [] ∧ TraceOf (source k v) [] ∧
 (∀ n, scanLoop (initial k v) (n+4) = scanLoop (vout k v) n) ∧
 (vout k v).offset = (source k v).utf8ByteSize ∧
 scanNextToken (vout k v) = .ok none := by
 have hs := word_filtered k v hk hv
 have hp := ExplicitWordParser.parsed_source k v hk hv
 have he := word_events k v
 obtain ⟨ts,ht,htr⟩ := word_fragment_trace k v hk hv
 have ht' : ts=expectedTokens k v := Except.ok.inj (ht.symm.trans hs)
 subst ts
 rw [he] at htr
 exact ⟨hs,hp,he,htr,fun n => ExplicitWordExecution.word_fold k v hk hv n,
  (value_eof k v hk.2 hv.2).1,(value_eof k v hk.2 hv.2).2⟩

#print axioms word_fragment_trace
#print axioms word_fragment_assurance
end L4YAML.Tests.Guards.ExplicitWordAssurance
