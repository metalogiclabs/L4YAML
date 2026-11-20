/- Bounded Row 19 repair check. Capstone: Blueprint 7.7.
The corrected research T grammar must preserve the four-byte plain scalar
and discharge its complete all-readings serialization obligation.
Base: e94baa39f828852390ff65f9441c4bb4253b9cfc. T implicitContinue is
explicit-document-only; the S grammar still has its known over-approximations.
This test does not certify a paired S/T repair or the universal capstone.
No source grammar or executable definition is changed by this test. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.TraceOf.UniqueFlow
public import L4YAML.Parser.Composition
import all Init.Data.Range.Basic
@[expose] public section Blanket

namespace L4YAML.Tests.Guards.RepairedPlainAlias
open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

def input : String := "a\n*x"
#guard input.toList = ['a', '\n', '*', 'x']
#guard input.utf8ByteSize = 4

abbrev p0 : SurfPos := ⟨['a', '\n', '*', 'x'], 0⟩
abbrev p1 : SurfPos := ⟨['\n', '*', 'x'], 1⟩
abbrev p2 : SurfPos := ⟨['*', 'x'], 0⟩
abbrev p3 : SurfPos := ⟨['x'], 1⟩
abbrev p4 : SurfPos := ⟨[], 2⟩

local macro "basic_cases" : tactic =>
  `(tactic| (repeat (first
    | contradiction
    | (solve | simp_all [p0,p1,p2,p3,p4])
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

lemma ssl0_end {t : SurfPos} (h : SSLComments p0 t) : t = p0 := by basic_cases
lemma sep0_end {n : Nat} {c : YamlContext} {t : SurfPos} (h : SSeparate n c p0 t) :
    t = p0 := by
  cases c <;> simp only [SSeparate] at h <;> basic_cases

def PlainFront (s : SurfPos) : Prop := s = p1 ∨ s = p3 ∨ s.chars = []
def Frontier (s : SurfPos) : Prop := s = p0 ∨ s = p2 ∨ s.chars = []

lemma pstep_front {n : Nat} {c : YamlContext} {s t : SurfPos}
    (h : PStep n c s t) (hs : PlainFront s) : PlainFront t := by
  have he := pstep_end h
  rcases hs with rfl | rfl | heof
  · right; left; simpa [stepEnd,skipWSP,skipWS,p1,p3] using he
  · right; right; simp [he,stepEnd,skipWSP,skipWS]
  · right; right; simp [he,stepEnd,skipWSP,skipWS,heof]

lemma psteps_front {n : Nat} {c : YamlContext} {s t : SurfPos}
    (h : GStar (PStep n c) s t) : PlainFront s → PlainFront t := by
  induction h with
  | nil => exact id
  | cons s u t hs ht ih => exact fun hf => ih (pstep_front hs hf)

lemma plain0_end {n : Nat} {c : YamlContext} {t : SurfPos}
    (h : SNsPlain n c p0 t) : PlainFront t := by
  obtain ⟨u, hf, ht⟩ := plain_steps h
  cases hf <;> exact psteps_front ht (Or.inl rfl)

lemma no_props0 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TCNsProperties n c p0 t ev) : False := by
  have hh := props_head h
  simp [p0] at hh

lemma flow0 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TFlowNode n c p0 t ev) : ev = [] ∧ PlainFront t := by
  cases h with
  | alias _ _ _ _ _ ha => cases ha.1
  | propsContent _ _ _ _ _ _ _ _ hp _ _ => exact False.elim (no_props0 hp)
  | propsEmpty _ _ _ _ _ hp => exact False.elim (no_props0 hp)
  | content _ _ _ _ _ hc =>
    cases hc with
    | plain _ _ _ _ hp => exact ⟨rfl, plain0_end hp⟩
    | flowSeq _ _ _ _ _ hs => cases hs <;> cases ‹GLit '[' p0 _›
    | flowMap _ _ _ _ _ hm => cases hm <;> cases ‹GLit '{' p0 _›
    | singleQ _ _ _ _ hq => cases hq <;> cases ‹GLit '\'' p0 _›
    | doubleQ _ _ _ _ hq => cases hq <;> cases ‹GLit '"' p0 _›

lemma no_colon_front {s t : SurfPos} (hs : PlainFront s) (h : GLit ':' s t) : False := by
  rcases hs with rfl | rfl | heof
  · cases h
  · cases h
  · cases h; simp_all

lemma inline_plain_front {s t : SurfPos} (hs : PlainFront s)
    (h : GOpt SSeparateInLine s t) : PlainFront t := by
  rcases hs with rfl | rfl | heof
  · cases h with
    | none => exact Or.inl rfl
    | some _ h => basic_cases
  · cases h with
    | none => exact Or.inr (Or.inl rfl)
    | some _ h => basic_cases
  · rcases s with ⟨cs,col⟩
    simp only at heof
    subst cs
    right; right
    have ht := L4YAML.Proofs.SurfaceSpan.gopt_suffix
      (fun _ _ => L4YAML.Proofs.SurfaceSpan.sSeparateInLine_suffix) h
    simpa using ht

lemma key0_end {t : SurfPos} {ev : List Event}
    (h : TImplicitKey p0 t ev) : PlainFront t := by
  cases h with
  | jsonKey s u t ev hf hw => exact inline_plain_front (flow0 hf).2 hw
  | yamlKey s u t hp hw => exact inline_plain_front (plain0_end hp) hw

lemma no_entry0 {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntry n p0 t ev) : False := by
  cases h <;> first
    | exact no_colon_front (key0_end ‹TImplicitKey p0 _ _›) ‹GLit ':' _ _›
    | cases ‹GLit _ p0 _›

lemma no_seq0 {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockSeqEntries n p0 t ev) : False := by
  cases h <;> cases ‹SIndent _ p0 _› <;> cases ‹GLit '-' p0 _›

lemma no_map0 {n : Nat} {t : SurfPos} {ev : List Event}
    (h : TBlockMapEntries n p0 t ev) : False := by
  cases h <;> cases ‹SIndent _ p0 _› <;> exact no_entry0 ‹TBlockMapEntry _ p0 _ _›

lemma comments_plain_front {s t : SurfPos} (hs : PlainFront s)
    (h : SSLComments s t) : Frontier t := by
  rcases hs with rfl | rfl | heof
  · have he : t = p2 := by basic_cases
    exact Or.inr (Or.inl he)
  · basic_cases
  · rcases s with ⟨cs,col⟩
    simp only at heof
    subst cs
    have he : t.chars = [] := by
      have ht := L4YAML.Proofs.SurfaceSpan.sslComments_suffix h
      simpa using ht
    exact Or.inr (Or.inr he)

lemma opt_props0 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TOpt (TSeq (Lift (SSeparate n c)) (TCNsProperties n c)) p0 t ev) :
    t = p0 ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl,rfl⟩
  | some _ _ _ ht =>
    cases ht with
    | mk _ u _ e1 e2 hs hp =>
      have he := sep0_end hs.1
      subst he
      exact False.elim (no_props0 hp)

lemma opt_props_sep0 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TOpt (TSeq (TCNsProperties n c) (Lift (SSeparate n c))) p0 t ev) :
    t = p0 ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl,rfl⟩
  | some _ _ _ ht =>
    cases ht with
    | mk _ u _ e1 e2 hp hs => exact False.elim (no_props0 hp)

lemma node0 {n : Nat} {c : YamlContext} {t : SurfPos} {ev : List Event}
    (h : TBlockNode n c p0 t ev) : Frontier t ∧ ev = [] := by
  cases h with
  | blockLiteral _ _ _ u v _ _ hs hp hl =>
    have hu := sep0_end hs; subst hu
    obtain ⟨hv,rfl⟩ := opt_props_sep0 hp; subst hv
    cases hl
  | blockFolded _ _ _ u v _ _ hs hp hl =>
    have hu := sep0_end hs; subst hu
    obtain ⟨hv,rfl⟩ := opt_props_sep0 hp; subst hv
    cases hl
  | blockSeq _ _ m _ u v _ _ _ hp hc hseq =>
    obtain ⟨hu,rfl⟩ := opt_props0 hp; subst hu
    have hv := ssl0_end hc; subst hv
    exact False.elim (no_seq0 hseq)
  | blockMap _ _ m _ u v _ _ _ hp hc hmap =>
    obtain ⟨hu,rfl⟩ := opt_props0 hp; subst hu
    have hv := ssl0_end hc; subst hv
    exact False.elim (no_map0 hmap)
  | flowInBlock _ _ _ u v _ _ hs hf hc =>
    have hu := sep0_end hs; subst hu
    obtain ⟨he,hv⟩ := flow0 hf
    exact ⟨comments_plain_front hv hc, he⟩
  | emptyNode _ _ _ _ hc => exact ⟨Or.inl (ssl0_end hc),rfl⟩

lemma prefix0_one {t : SurfPos} (h : SLDocumentPrefix p0 t) : t = p0 := by
  cases h <;> basic_cases

lemma prefix0 {s t : SurfPos} (h : GStar SLDocumentPrefix s t) : s = p0 → t = p0 := by
  induction h with
  | nil => exact id
  | cons s u t hp ht ih =>
    intro he; subst he
    exact ih (prefix0_one hp)

lemma prefix_front_one {s t : SurfPos} (hs : Frontier s)
    (h : SLDocumentPrefix s t) : Frontier t := by
  rcases hs with rfl | rfl | heof
  · exact Or.inl (prefix0_one h)
  · have he : t = p2 := by cases h <;> basic_cases
    exact Or.inr (Or.inl he)
  · right; right
    cases h with
    | comments s t hg =>
      have ht := L4YAML.Proofs.SurfaceSpan.gstar_suffix
        (fun _ _ => L4YAML.Proofs.SurfaceSpan.slComment_suffix) hg
      simpa [heof] using ht
    | bom => simp_all

lemma prefix_front {s t : SurfPos} (h : GStar SLDocumentPrefix s t) :
    Frontier s → Frontier t := by
  induction h with
  | nil => exact id
  | cons s u t hp ht ih => exact fun hs => ih (prefix_front_one hs hp)

lemma no_suffix {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TLDocumentSuffix s t ev) : False := by
  cases h with
  | mk s u t hm hc =>
    rcases hs with rfl | rfl | heof
    · cases hm
    · cases hm
    · cases hm; simp_all

lemma suffix_star {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TStar TLDocumentSuffix s t ev) : t = s ∧ ev = [] := by
  cases h with
  | nil => exact ⟨rfl,rfl⟩
  | cons _ _ _ _ _ hp _ => exact False.elim (no_suffix hs hp)

lemma no_suffix_plus {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TPlus TLDocumentSuffix s t ev) : False := by
  cases h with
  | mk _ _ _ _ _ hp _ => exact no_suffix hs hp

lemma any0 {t : SurfPos} {ev : List Event}
    (h : TLAnyDocument p0 t ev) : Frontier t ∧ ev = [] := by
  cases h with
  | bare _ _ _ hb => cases hb with | mk _ _ _ hn => exact node0 hn
  | explicit _ _ _ he => cases he with | withContent _ _ _ _ hm _ => cases hm
  | directive _ _ _ hd =>
    cases hd with
    | mk _ _ _ _ _ _ hp _ _ =>
      cases hp with
      | mk _ _ _ _ _ hl _ => cases hl.1

lemma opt_any0 {t : SurfPos} {ev : List Event}
    (h : TOpt TLAnyDocument p0 t ev) : Frontier t ∧ ev = [] := by
  cases h with
  | none => exact ⟨Or.inl rfl,rfl⟩
  | some _ _ _ hd => exact any0 hd

lemma explicit_opt {s t : SurfPos} {ev : List Event} (hs : Frontier s)
    (h : TOpt TLExplicitDocument s t ev) : t = s ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl,rfl⟩
  | some _ _ _ he =>
    cases he with
    | withContent _ _ _ _ hm _ =>
      rcases hs with rfl | rfl | heof
      · cases hm
      · cases hm
      · cases hm; simp_all

lemma stream_empty_events {s t : SurfPos} {ev : List Event}
    (h : TLYamlStream s t ev) : s = p0 → Frontier t ∧ ev = [] := by
  induction h with
  | single s a b t e1 e2 hp hd ht =>
    intro he; subst he
    have ha := prefix0 hp rfl; subst ha
    obtain ⟨hb,he1⟩ := opt_any0 hd
    obtain ⟨ht',he2⟩ := suffix_star hb ht
    subst ht'
    exact ⟨hb,by simp [he1,he2]⟩
  | suffixContinue s a b c d t e0 e1 e2 e3 hprev hplus hp hd ht ih =>
    intro he
    exact False.elim (no_suffix_plus (ih he).1 hplus)
  | implicitContinue s a b c t e0 e1 e2 hprev hp hd ht ih =>
    intro he
    obtain ⟨ha,he0⟩ := ih he
    have hb := prefix_front hp ha
    obtain ⟨hc,he1⟩ := explicit_opt hb hd
    subst hc
    obtain ⟨ht',he2⟩ := suffix_star hb ht
    subst ht'
    exact ⟨hb,by simp [he0,he1,he2]⟩

/-- Every annotated reading of the repaired four-byte input has no events. -/
lemma all_traces_empty (ev : List Event) (h : TraceOf input ev) : ev = [] := by
  obtain ⟨col, hs⟩ := h
  exact (stream_empty_events hs (by rfl)).2

/-- Full all-readings serialization guarantee, with no coherence premise. -/
lemma trace_well_formed : TraceWellFormed input := by
  intro ev ht
  rw [all_traces_empty ev ht]
  trivial

private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma nsc_star : isNsChar '*' := by unfold isNsChar; decide
private lemma nsc_x : isNsChar 'x' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

/-- Nonvacuity: the corrected grammar retains the intended plain reading. -/
lemma trace_exists : TraceOf input [] :=
  ⟨2, .single p0 p0 p4 p4 [] [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _
      (.flowInBlock 0 .blockIn p0 p0 p4 p4 []
        (.inline 0 _ _ (.startOfLine _))
        (.content 0 .flowOut p0 p4 [] (.plain 0 .flowOut p0 p4
          (SNsPlainMultiLine.mk 0 .flowOut p0 p1 p4
            (SNsPlainOneLine.mk .flowOut p0 p1 p1
              (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
            (.cons p1 p4 p4
              (SSNsPlainNextLine.mk 0 .flowOut p1 p1 p2 p2 p2 p3 p4
                (.nil _) (SBBreak.lf _ 1) (.nil _)
                (SFlowLinePrefix.mk 0 p2 p2 p2 (.zero _) (.none _))
                (SNsPlainChar.safe .flowOut '*' _ 0 nsc_star (by decide) (by decide))
                (.cons p3 p4 p4
                  (SNbNsPlainInLineEntry.mk .flowOut p3 p3 p4 (.nil _)
                    (SNsPlainChar.safe .flowOut 'x' _ 1 nsc_x (by decide) (by decide)))
                  (.nil _)))
              (.nil _)))))
        (.withComment _ _ _ (.noSep _ _ (.eof 2)) (.nil _))))))
    (.nil _)⟩

lemma parser_accepts_bit : (TokenParser.parseYaml input).isOk = true := by cbv

lemma parser_accepts : ∃ docs, TokenParser.parseYaml input = .ok docs := by
  have h := parser_accepts_bit
  cases hs : TokenParser.parseYaml input with
  | ok docs => exact ⟨docs,rfl⟩
  | error e => rw [hs] at h; cases h

/-- The old four-byte obstruction is removed on the corrected T grammar,
while both actual parser acceptance and grammar nonvacuity are retained. -/
lemma repaired_witness :
    (∃ docs, TokenParser.parseYaml input = .ok docs) ∧
      TraceOf input [] ∧ TraceWellFormed input :=
  ⟨parser_accepts, trace_exists, trace_well_formed⟩

lemma empty_parser_control : (TokenParser.parseYaml "").isOk = true := by cbv
lemma empty_trace_control : TraceOf "" [] := traceOf_empty

#print axioms all_traces_empty
#print axioms trace_well_formed
#print axioms trace_exists
#print axioms parser_accepts_bit
#print axioms parser_accepts
#print axioms repaired_witness
#print axioms empty_parser_control
#print axioms empty_trace_control

end L4YAML.Tests.Guards.RepairedPlainAlias
end Blanket
