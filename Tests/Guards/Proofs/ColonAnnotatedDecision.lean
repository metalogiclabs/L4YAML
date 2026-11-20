/- Exact annotated-grammar decision experiment. Capstone: Blueprint 7.7,
via validation of the S3 scanner-to-trace obligation before global induction.
The input bytes are pinned below. No scanner or grammar definition is changed. -/
module
public import Tests.Guards.Proofs.ColonTwoBareDocuments
public import L4YAML.Proofs.Serialization.TraceOf.UniqueFlow
public import L4YAML.Proofs.Serialization.TokenEvents
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.ColonAnnotatedDecision
open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Tests.Guards.ColonTwoBareDocuments
set_option autoImplicit true
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

def exactInput : String := "? -\n  :"
#guard exactInput.toList = ['?', ' ', '-', '\n', ' ', ' ', ':']
#guard exactInput.utf8ByteSize = 7
abbrev p4a : SurfPos := ⟨[' ', ':'], 1⟩

lemma indent4 {n : Nat} {t : SurfPos} (h : SIndent n p4 t) :
    (n = 0 ∧ t = p4) ∨ (n = 1 ∧ t = p4a) ∨ (n = 2 ∧ t = p5) := by
  cases h with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ n rest col t h =>
    cases h with
    | zero => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | succ n rest col t h =>
      cases h with
      | zero => exact Or.inr (Or.inr ⟨rfl, rfl⟩)

lemma indent1 {n : Nat} {t : SurfPos} (h : SIndent n p1 t) :
    (n = 0 ∧ t = p1) ∨ (n = 1 ∧ t = p2) := by
  cases h with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ n rest col t h =>
    cases h with
    | zero => exact Or.inr ⟨rfl, rfl⟩

lemma no_flow_at {n : Nat} {c : YamlContext} {s t : SurfPos} {ev : List Event}
    (hs : s = p0 ∨ s = p1 ∨ s = p2 ∨ s = p3 ∨ s = p4 ∨ s = p4a ∨ s = p5)
    (h : TFlowNode n c s t ev) : False := by
  have hh := node_head h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases c <;>
    simp [p0,p1,p2,p3,p4,p4a,p5,ContentHead,isNsPlainSafe,isNsChar,isIndicatorProp,
      isLineBreakProp,isWhiteSpaceProp,isLineFeedProp,isCarriageReturnProp,isSpaceProp,isTabProp] at hh

lemma no_props_at {n : Nat} {c : YamlContext} {s t : SurfPos} {ev : List Event}
    (hs : s = p0 ∨ s = p1 ∨ s = p2 ∨ s = p3 ∨ s = p4 ∨ s = p4a ∨ s = p5)
    (h : TCNsProperties n c s t ev) : False := by
  have hh := props_head h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [p0,p1,p2,p3,p4,p4a,p5] at hh

local macro "basic_cases" : tactic =>
  `(tactic| (repeat (first
    | contradiction
    | (solve | simp_all [p0,p1,p2,p3,p4,p4a,p5,p6])
    | cases ‹SSWhite _ _›
    | cases ‹SBBreak _ _›
    | cases ‹GLit _ _ _›
    | cases ‹SCNbCommentText _ _›
    | cases ‹SBComment _ _›
    | cases ‹GOpt SCNbCommentText _ _›
    | cases ‹SSeparateInLine _ _›
    | cases ‹GPlus SSWhite _ _›
    | cases ‹GStar SSWhite _ _›
    | cases ‹SSBComment _ _›
    | cases ‹SLComment _ _›
    | cases ‹GStar SLComment _ _›
    | cases ‹SSLComments _ _›
    | cases ‹SIndent _ _ _›
    | cases ‹GOpt SSeparateInLine _ _›
    | cases ‹SFlowLinePrefix _ _ _›
    | cases ‹SSeparateLines _ _ _›
    )))

lemma ssl0_end {t : SurfPos} (h : SSLComments p0 t) : t = p0 := by
  basic_cases
lemma ssl1_false {t : SurfPos} (h : SSLComments p1 t) : False := by
  basic_cases
lemma ssl2_false {t : SurfPos} (h : SSLComments p2 t) : False := by
  basic_cases
lemma ssl3_end {t : SurfPos} (h : SSLComments p3 t) : t = p4 := by
  basic_cases
lemma ssl4_end {t : SurfPos} (h : SSLComments p4 t) : t = p4 := by
  basic_cases
lemma sep0_end {n : Nat} {c : YamlContext} {t : SurfPos} (h : SSeparate n c p0 t) : t = p0 := by
  cases c <;> simp only [SSeparate] at h <;> basic_cases
lemma sep1_end {n : Nat} {c : YamlContext} {t : SurfPos} (h : SSeparate n c p1 t) : t = p2 := by
  cases c <;> simp only [SSeparate] at h <;> basic_cases
lemma sep3_impossible {n : Nat} {c : YamlContext} {t : SurfPos}
    (hn : 3 ≤ n) (h : SSeparate n c p3 t) : False := by
  cases c <;> simp only [SSeparate] at h <;> basic_cases <;> omega

lemma no_implicit_at {s t : SurfPos} {ev : List Event}
    (hs : s = p0 ∨ s = p1 ∨ s = p2 ∨ s = p3 ∨ s = p4 ∨ s = p4a ∨ s = p5)
    (h : TImplicitKey s t ev) : False := by
  cases h with
  | jsonKey s u t ev hf hw => exact no_flow_at hs hf
  | yamlKey s u t hp hw =>
    have hh := plain_contentHead hp
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [p0,p1,p2,p3,p4,p5,ContentHead,isNsPlainSafe,isNsChar,isIndicatorProp,
        isLineBreakProp,isWhiteSpaceProp,isLineFeedProp,isCarriageReturnProp,isSpaceProp,isTabProp] at hh

lemma no_map_entry_dash {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntry n p2 t ev) : False := by
  cases h <;> first
    | exact no_implicit_at (by simp) ‹TImplicitKey p2 _ _›
    | cases ‹GLit _ p2 _›
lemma no_map_entry_newline {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntry n p3 t ev) : False := by
  cases h <;> first
    | exact no_implicit_at (by simp) ‹TImplicitKey p3 _ _›
    | cases ‹GLit _ p3 _›
lemma no_map_entry_space {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntry n p4 t ev) : False := by
  cases h <;> first
    | exact no_implicit_at (by simp) ‹TImplicitKey p4 _ _›
    | cases ‹GLit _ p4 _›
lemma no_seq4 {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockSeqEntries n p4 t ev) : False := by
  cases h <;> basic_cases
lemma no_map4_gt {n : Nat} {t : SurfPos} {ev : List Event}
    (hn : 3 ≤ n) (h : TBlockMapEntries n p4 t ev) : False := by
  cases h <;> basic_cases <;> omega

lemma opt_props_tail_none {n : Nat} {c : YamlContext} {s t : SurfPos} {ev : List Event}
    (hs : s = p0 ∨ s = p1 ∨ s = p2 ∨ s = p3 ∨ s = p4 ∨ s = p4a ∨ s = p5)
    (h : TOpt (TSeq (TCNsProperties n c) (Lift (SSeparate n c))) s t ev) :
    t = s ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hh =>
    cases hh with
    | mk _ _ _ _ _ hp _ => exact False.elim (no_props_at hs hp)

lemma opt_prefix_props0 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TOpt (TSeq (Lift (SSeparate n c)) (TCNsProperties n c)) p0 t ev) :
    t = p0 ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hh =>
    cases hh with
    | mk _ _ _ _ _ hp hq =>
      have e := sep0_end hp.1
      subst e
      exact False.elim (no_props_at (by simp) hq)
lemma opt_prefix_props1 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TOpt (TSeq (Lift (SSeparate n c)) (TCNsProperties n c)) p1 t ev) :
    t = p1 ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hh =>
    cases hh with
    | mk _ _ _ _ _ hp hq =>
      have e := sep1_end hp.1
      subst e
      exact False.elim (no_props_at (by simp) hq)
lemma opt_prefix_props3 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (hn : 3 ≤ n)
    (h : TOpt (TSeq (Lift (SSeparate n c)) (TCNsProperties n c)) p3 t ev) :
    t = p3 ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hh =>
    cases hh with
    | mk _ _ _ _ _ hp _ => exact False.elim (sep3_impossible hn hp.1)

lemma node3_end {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (hn : 3 ≤ n) (h : TBlockNode n c p3 t ev) : t = p4 := by
  cases h with
  | blockLiteral _ _ _ _ _ _ _ hs _ _ => exact False.elim (sep3_impossible hn hs)
  | blockFolded _ _ _ _ _ _ _ hs _ _ => exact False.elim (sep3_impossible hn hs)
  | blockSeq _ _ _ _ _ _ _ _ _ hp hc he =>
    obtain ⟨rfl, rfl⟩ := opt_prefix_props3 hn hp
    have e := ssl3_end hc
    subst e
    exact False.elim (no_seq4 he)
  | blockMap _ _ _ _ _ _ _ _ _ hp hc he =>
    obtain ⟨rfl, rfl⟩ := opt_prefix_props3 hn hp
    have e := ssl3_end hc
    subst e
    exact False.elim (no_map4_gt (by omega) he)
  | flowInBlock _ _ _ _ _ _ _ hs _ _ => exact False.elim (sep3_impossible hn hs)
  | emptyNode _ _ _ _ hc => exact ssl3_end hc

lemma indented3_end {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (hn : 2 ≤ n) (h : TBlockIndented n c p3 t ev) : t = p4 := by
  cases h with
  | compactSeq _ _ _ _ _ _ _ hi hs =>
    cases hi
    cases hs with
    | mk _ _ _ _ _ _ _ hl _ _ _ => cases hl
  | compactMap _ _ _ _ _ _ _ hi hm =>
    cases hi
    cases hm with
    | mk _ _ _ _ _ _ he _ => exact False.elim (no_map_entry_newline he)
  | node _ _ _ _ _ hn => exact node3_end (by omega) hn
  | empty _ _ _ _ hc => exact ssl3_end hc

lemma compact2_end {t : SurfPos} {ev : List Event}
    (h : TCompactSeq 2 p2 t ev) : t = p4 := by
  cases h with
  | mk _ _ _ _ _ _ _ hl hnot hi ht =>
    cases hl
    have e := indented3_end (by decide) hi
    subst e
    cases ht with
    | nil => rfl
    | cons => basic_cases

lemma no_map_entry_p1 {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntry n p1 t ev) : False := by
  cases h <;> first
    | exact no_implicit_at (by simp) ‹TImplicitKey p1 _ _›
    | cases ‹GLit _ p1 _›

lemma node1_false {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TBlockNode n c p1 t ev) : False := by
  cases h with
  | blockLiteral _ _ _ _ _ _ _ hs hp hl =>
    have e := sep1_end hs
    subst e
    obtain ⟨rfl, rfl⟩ := opt_props_tail_none (by simp) hp
    cases hl
  | blockFolded _ _ _ _ _ _ _ hs hp hl =>
    have e := sep1_end hs
    subst e
    obtain ⟨rfl, rfl⟩ := opt_props_tail_none (by simp) hp
    cases hl
  | blockSeq _ _ _ _ _ _ _ _ _ hp hc he =>
    obtain ⟨rfl, rfl⟩ := opt_prefix_props1 hp
    exact ssl1_false hc
  | blockMap _ _ _ _ _ _ _ _ _ hp hc he =>
    obtain ⟨rfl, rfl⟩ := opt_prefix_props1 hp
    exact ssl1_false hc
  | flowInBlock _ _ _ _ _ _ _ hs hf hc =>
    have e := sep1_end hs
    subst e
    exact no_flow_at (by simp) hf
  | emptyNode _ _ _ _ hc => exact ssl1_false hc

lemma key0_end {t : SurfPos} {ev : List Event}
    (h : TBlockIndented 0 .blockOut p1 t ev) : t = p4 := by
  cases h with
  | compactSeq _ _ _ _ _ _ _ hi hs =>
    rcases indent1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hs
      cases ‹GLit '-' p1 _›
    · exact compact2_end hs
  | compactMap _ _ _ _ _ _ _ hi hm =>
    rcases indent1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hm
      exact False.elim (no_map_entry_p1 ‹TBlockMapEntry _ p1 _ _›)
    · cases hm
      exact False.elim (no_map_entry_dash ‹TBlockMapEntry _ p2 _ _›)
  | node _ _ _ _ _ hn => exact False.elim (node1_false hn)
  | empty _ _ _ _ hc => exact False.elim (ssl1_false hc)

lemma entry0_end {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntry 0 p0 t ev) : t = p4 := by
  cases h with
  | explicit _ _ _ _ _ _ _ _ _ hl hk hi hc hv =>
    cases hl
    have e := key0_end hk
    subst e
    cases hi
    cases hc
  | explicitEmpty _ _ _ _ _ hl hk =>
    cases hl
    exact key0_end hk
  | implicitKeyNode _ _ _ _ _ _ _ hk _ _ => exact False.elim (no_implicit_at (by simp) hk)
  | implicitKeyEmpty _ _ _ _ _ _ hk _ _ => exact False.elim (no_implicit_at (by simp) hk)
  | emptyKeyNode _ _ _ _ _ hl _ => cases hl
  | emptyKeyEmpty _ _ _ _ hl _ => cases hl

lemma map4_zero_false {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntries 0 p4 t ev) : False := by
  cases h with
  | single _ _ _ _ _ hi he =>
    cases hi
    exact no_map_entry_space he
  | cons _ _ _ _ _ _ _ hi he ht =>
    cases hi
    exact no_map_entry_space he

lemma map0_end {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntries n p0 t ev) : t = p4 := by
  cases h with
  | single _ _ _ _ _ hi he =>
    cases hi
    exact entry0_end he
  | cons _ _ _ _ _ _ _ hi he ht =>
    cases hi
    have e := entry0_end he
    subst e
    exact False.elim (map4_zero_false ht)

lemma no_seq0 {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockSeqEntries n p0 t ev) : False := by
  cases h <;> basic_cases

lemma node0_end {t : SurfPos} {ev : List Event}
    (h : TBlockNode 0 .blockIn p0 t ev) : t = p0 ∨ t = p4 := by
  cases h with
  | blockLiteral _ _ _ _ _ _ _ hs hp hl =>
    have e := sep0_end hs
    subst e
    obtain ⟨rfl, rfl⟩ := opt_props_tail_none (by simp) hp
    cases hl
  | blockFolded _ _ _ _ _ _ _ hs hp hl =>
    have e := sep0_end hs
    subst e
    obtain ⟨rfl, rfl⟩ := opt_props_tail_none (by simp) hp
    cases hl
  | blockSeq _ _ _ _ _ _ _ _ _ hp hc he =>
    obtain ⟨rfl, rfl⟩ := opt_prefix_props0 hp
    have e := ssl0_end hc
    subst e
    exact False.elim (no_seq0 he)
  | blockMap _ _ _ _ _ _ _ _ _ hp hc he =>
    obtain ⟨rfl, rfl⟩ := opt_prefix_props0 hp
    have e := ssl0_end hc
    subst e
    exact Or.inr (map0_end he)
  | flowInBlock _ _ _ _ _ _ _ hs hf hc =>
    have e := sep0_end hs
    subst e
    exact False.elim (no_flow_at (by simp) hf)
  | emptyNode _ _ _ _ hc => exact Or.inl (ssl0_end hc)

def Frontier (s : SurfPos) : Prop := s = p0 ∨ s = p4

lemma prefix_one_end {s t : SurfPos} (hs : Frontier s)
    (h : SLDocumentPrefix s t) : t = s := by
  rcases hs with rfl | rfl <;> cases h <;> basic_cases

lemma prefix_end {s t : SurfPos} (h : GStar SLDocumentPrefix s t) :
    Frontier s → t = s := by
  induction h with
  | nil => intro _; rfl
  | cons a b d hp ht ih =>
    intro hs
    have e := prefix_one_end hs hp
    subst e
    exact ih hs

lemma no_suffix_frontier {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TLDocumentSuffix s t ev) : False := by
  cases h with
  | mk s u t hm hc =>
    rcases hs with rfl | rfl <;> cases hm
lemma suffix_star_end {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TStar TLDocumentSuffix s t ev) : t = s := by
  cases h with
  | nil => rfl
  | cons _ _ _ _ _ hp _ => exact False.elim (no_suffix_frontier hs hp)
lemma no_suffix_plus {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TPlus TLDocumentSuffix s t ev) : False := by
  cases h with
  | mk _ _ _ _ _ hp _ => exact no_suffix_frontier hs hp

lemma any0_end {t : SurfPos} {ev : List Event}
    (h : TLAnyDocument p0 t ev) : Frontier t := by
  cases h with
  | bare _ _ _ hb =>
    cases hb with
    | mk _ _ _ hn => exact node0_end hn
  | explicit _ _ _ he =>
    cases he with
    | withContent _ _ _ _ hm _ => cases hm
  | directive _ _ _ hd =>
    cases hd with
    | mk _ _ _ _ _ _ hp _ _ =>
      cases hp with
      | mk _ _ _ _ _ hl _ =>
        cases hl.1
lemma opt_any0_end {t : SurfPos} {ev : List Event}
    (h : TOpt TLAnyDocument p0 t ev) : Frontier t := by
  cases h with
  | none => exact Or.inl rfl
  | some _ _ _ hd => exact any0_end hd

lemma explicit_opt_end {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TOpt TLExplicitDocument s t ev) : t = s := by
  cases h with
  | none => rfl
  | some _ _ _ he =>
    cases he with
    | withContent _ _ _ _ hm _ => rcases hs with rfl | rfl <;> cases hm

lemma stream_frontier {s t : SurfPos} {ev : List Event}
    (h : TLYamlStream s t ev) : s = p0 → Frontier t := by
  induction h with
  | single s a b t e1 e2 hp hd ht =>
    intro heq
    subst heq
    have e := prefix_end hp (Or.inl rfl)
    subst e
    have hb := opt_any0_end hd
    have et := suffix_star_end hb ht
    subst et
    exact hb
  | suffixContinue s a b c d t e0 e1 e2 e3 hprev hplus hp hd ht ih =>
    intro heq
    exact False.elim (no_suffix_plus (ih heq) hplus)
  | implicitContinue s a b c t e0 e1 e2 hprev hp hd ht ih =>
    intro heq
    have ha := ih heq
    have eb := prefix_end hp ha
    subst eb
    have ec := explicit_opt_end ha hd
    subst ec
    have et := suffix_star_end ha ht
    subst et
    exact ha

/-- Complete annotated-grammar nonmembership for the exact seven-byte body.
This quantifies over EVERY event list and terminal column; it does not rely
on the token parser's rejection or the weakened source grammar. -/
lemma exact_body_has_no_trace (ev : List Event) : ¬ TraceOf exactInput ev := by
  rintro ⟨col, h⟩
  have hf := stream_frontier h (by rfl)
  rcases hf with h0 | h4
  · cases h0
  · cases h4

/-- Positive control: the actual annotated grammar admits the empty stream. -/
lemma empty_trace_control : TraceOf "" [] := traceOf_empty

/-- The old native scanner truly accepts these same seven bytes.
Kernel reduction is used, not an assertion based on parser behavior. -/
lemma exact_scanner_accepts :
    ∃ ts, L4YAML.Scanner.scanFiltered exactInput = .ok ts := by
  have hOk : (L4YAML.Scanner.scanFiltered exactInput).isOk = true := by cbv
  cases hs : L4YAML.Scanner.scanFiltered exactInput with
  | ok ts => exact ⟨ts, rfl⟩
  | error e =>
    rw [hs] at hOk
    change false = true at hOk
    cases hOk

/-- The universally-scanner-qualified S3 claim is false on this frozen
runtime/annotated-grammar combination. The witness is the exact seven-byte
body, and nonmembership quantifies over the scanner's actual event list. -/
lemma universal_scan_trace_refuted :
    ¬ (∀ (input : String) (ts : Array (Positioned YamlToken)),
      L4YAML.Scanner.scanFiltered input = .ok ts →
      TraceOf input (L4YAML.Proofs.Serialization.TokenEvents.tokenEvents ts)) := by
  intro h
  obtain ⟨ts, hs⟩ := exact_scanner_accepts
  exact exact_body_has_no_trace _ (h exactInput ts hs)

#print axioms L4YAML.Tests.Guards.ColonAnnotatedDecision.empty_trace_control
#print axioms L4YAML.Tests.Guards.ColonAnnotatedDecision.exact_scanner_accepts
#print axioms L4YAML.Tests.Guards.ColonAnnotatedDecision.universal_scan_trace_refuted

#print axioms L4YAML.Tests.Guards.ColonAnnotatedDecision.exact_body_has_no_trace

end L4YAML.Tests.Guards.ColonAnnotatedDecision
end Blanket
