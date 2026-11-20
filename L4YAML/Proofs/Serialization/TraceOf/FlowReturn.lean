/- Capstone 7.7 / S3: preserve the source-bound return obligation at the
base opener. Return is an obligation over the actual completed source span
and events. Frame operations reuse FlowWalk; the native arms reuse the
corresponding ContentBridge proofs with this stronger carrier.

Verification boundary: return_first and return_explicit fund the stream
return from their actual source routes. FlowReturnNative consumes the funded
return on a closed scanner-to-directive path. The remaining block-context
births and the global paired scanLoop invariant are still obligations.
This module is experimental and is not in the serialization umbrella. -/
module
public import L4YAML.Proofs.Serialization.TraceOf.RightWallContent

@[expose] public section Blanket
namespace L4YAML.Proofs.Serialization.TraceOf.FlowReturn
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.Serialization.TraceOf.FlowWalk
open L4YAML.Proofs.Serialization.TraceOf.DocBridge
open L4YAML.Proofs.StreamAccum (FrameTail)

inductive FlowOpenR (n : Nat) (Return : SurfPos → List Event → Prop) :
    Nat → Array Bool → Array Bool → FrameTail → SurfPos → SurfPos → List Event → Prop where
  | seqBase (sp_before sp_br sp_open sp_es sp_cur : SurfPos) (tl : FrameTail) (ev : List Event)
      (h_open : GLit '[' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es)
      (st : TSeqFrame n (inFlowCtx .flowOut) tl sp_es sp_cur ev)
      (returnTo : ∀ finish events, TFlowContent n .flowOut sp_br finish events → Return finish events) :
      FlowOpenR n Return 1 #[true] #[false] tl sp_before sp_cur ev
  | mapBase (sp_before sp_br sp_open sp_es sp_cur : SurfPos) (tl : FrameTail) (ev : List Event)
      (h_open : GLit '{' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es)
      (st : TMapFrame n (inFlowCtx .flowOut) tl sp_es sp_cur ev)
      (returnTo : ∀ finish events, TFlowContent n .flowOut sp_br finish events → Return finish events) :
      FlowOpenR n Return 1 #[false] #[false] tl sp_before sp_cur ev
  /-- Item 517: the mask `km` is the T face of `FlowOpenStack`'s key-map — bit `b` of a nest is
      WHETHER THE PARENT'S TAIL WAS `.colon` when the nest opened (the nest is a pair's value), a
      projection of the frame's own `tl_par` (Rule 8); the base's bit is `false` (block context).
      `TFlowStackK` couples it to the scanner by `KmSound sc km kc`, the S side's own obligation. -/
  | seqNest (d : Nat) (ks km : Array Bool) (b : Bool) (tl_par tl : FrameTail)
      (sp_before sp_par sp_br sp_open sp_es sp_cur : SurfPos) (ev_par ev : List Event)
      (parent : FlowOpenR n Return d ks km tl_par sp_before sp_par ev_par)
      (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
      (h_tail : ∀ kj, tl_par ≠ .value kj)
      (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
      (h_open : GLit '[' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TSeqFrame n .flowIn tl sp_es sp_cur ev) :
      FlowOpenR n Return (d + 1) (ks.push true) (km.push b) tl sp_before sp_cur (ev_par ++ ev)
  | mapNest (d : Nat) (ks km : Array Bool) (b : Bool) (tl_par tl : FrameTail)
      (sp_before sp_par sp_br sp_open sp_es sp_cur : SurfPos) (ev_par ev : List Event)
      (parent : FlowOpenR n Return d ks km tl_par sp_before sp_par ev_par)
      (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
      (h_tail : ∀ kj, tl_par ≠ .value kj)
      (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
      (h_open : GLit '{' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TMapFrame n .flowIn tl sp_es sp_cur ev) :
      FlowOpenR n Return (d + 1) (ks.push false) (km.push b) tl sp_before sp_cur (ev_par ++ ev)
  /-- A nest opened under a held property run (`[&a [b]]`, item 474): the parent, the lead to the
      run, the run's `TCNsProperties` twin and its separation to the bracket (`&a[` glued is what
      the scanner refuses), then the child as `seqNest`; at the close the run decorates the child
      (`receivePropsContent`), so the trace is `ev_par ++ (ev_p ++ ev)`. -/
  | seqNestProps (d : Nat) (ks km : Array Bool) (b : Bool) (tl_par tl : FrameTail)
      (sp_before sp_par sp_p sp_end sp_br sp_open sp_es sp_cur : SurfPos) (ev_par ev_p ev : List Event)
      (parent : FlowOpenR n Return d ks km tl_par sp_before sp_par ev_par)
      (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
      (h_tail : ∀ kj, tl_par ≠ .value kj)
      (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
      (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
      (h_psep : SSeparate n .flowIn sp_end sp_br)
      (h_open : GLit '[' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TSeqFrame n .flowIn tl sp_es sp_cur ev) :
      FlowOpenR n Return (d + 1) (ks.push true) (km.push b) tl sp_before sp_cur (ev_par ++ (ev_p ++ ev))
  | mapNestProps (d : Nat) (ks km : Array Bool) (b : Bool) (tl_par tl : FrameTail)
      (sp_before sp_par sp_p sp_end sp_br sp_open sp_es sp_cur : SurfPos) (ev_par ev_p ev : List Event)
      (parent : FlowOpenR n Return d ks km tl_par sp_before sp_par ev_par)
      (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
      (h_tail : ∀ kj, tl_par ≠ .value kj)
      (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
      (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
      (h_psep : SSeparate n .flowIn sp_end sp_br)
      (h_open : GLit '{' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TMapFrame n .flowIn tl sp_es sp_cur ev) :
      FlowOpenR n Return (d + 1) (ks.push false) (km.push b) tl sp_before sp_cur (ev_par ++ (ev_p ++ ev))


variable {Return : SurfPos → List Event → Prop}

lemma FlowOpenR.retrace {n D : Nat} {ks km : Array Bool} {tl : FrameTail} {a b : SurfPos}
    {ev ev' : List Event} (h : ev = ev') (st : FlowOpenR n Return D ks km tl a b ev) :
    FlowOpenR n Return D ks km tl a b ev' :=
  h ▸ st

lemma FlowOpenR.liftTop {n D : Nat} {ks km : Array Bool} {tl tl' : FrameTail}
    {sp_block sp_flow sp_new : SurfPos} {ev delta : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (fs : ∀ {sp_open sp_es : SurfPos} {ev_f : List Event},
      GOpt (SSeparate n .flowIn) sp_open sp_es → TSeqFrame n .flowIn tl sp_es sp_flow ev_f →
      ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
        TSeqFrame n .flowIn tl' sp_es' sp_new (ev_f ++ delta))
    (fm : ∀ {sp_open sp_es : SurfPos} {ev_f : List Event},
      GOpt (SSeparate n .flowIn) sp_open sp_es → TMapFrame n .flowIn tl sp_es sp_flow ev_f →
      ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
        TMapFrame n .flowIn tl' sp_es' sp_new (ev_f ++ delta)) :
    FlowOpenR n Return D ks km tl' sp_block sp_new (ev ++ delta) := by
  cases h with
  | seqBase sp_before sp_br sp_open sp_es sp_cur tl ev h_open h_sep st returnTo =>
    obtain ⟨sp_es', h_sep', st'⟩ := fs h_sep st
    exact .seqBase _ _ _ _ _ _ _ h_open h_sep' st' returnTo
  | mapBase sp_before sp_br sp_open sp_es sp_cur tl ev h_open h_sep st returnTo =>
    obtain ⟨sp_es', h_sep', st'⟩ := fm h_sep st
    exact .mapBase _ _ _ _ _ _ _ h_open h_sep' st' returnTo
  | seqNest d ks km b tl_par tl sp_before sp_par sp_br sp_open sp_es sp_cur ev_par ev parent h_b h_tail h_lead h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fs h_sep st
    exact FlowOpenR.retrace (List.append_assoc _ _ _).symm
      (.seqNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_open h_sep' st')
  | mapNest d ks km b tl_par tl sp_before sp_par sp_br sp_open sp_es sp_cur ev_par ev parent h_b h_tail h_lead h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fm h_sep st
    exact FlowOpenR.retrace (List.append_assoc _ _ _).symm
      (.mapNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_open h_sep' st')
  | seqNestProps d ks km b tl_par tl sp_before sp_par sp_p sp_end sp_br sp_open sp_es sp_cur ev_par ev_p ev
      parent h_b h_tail h_lead h_props h_psep h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fs h_sep st
    exact FlowOpenR.retrace
      (show ev_par ++ (ev_p ++ (ev ++ delta)) = (ev_par ++ (ev_p ++ ev)) ++ delta by
        simp only [List.append_assoc])
      (.seqNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_props h_psep h_open h_sep' st')
  | mapNestProps d ks km b tl_par tl sp_before sp_par sp_p sp_end sp_br sp_open sp_es sp_cur ev_par ev_p ev
      parent h_b h_tail h_lead h_props h_psep h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fm h_sep st
    exact FlowOpenR.retrace
      (show ev_par ++ (ev_p ++ (ev ++ delta)) = (ev_par ++ (ev_p ++ ev)) ++ delta by
        simp only [List.append_assoc])
      (.mapNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_props h_psep h_open h_sep' st')

lemma FlowOpenR.receiveNode {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_ne : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n) :
    FlowOpenR n Return D ks km (.value kj) sp_block sp_ne (ev ++ ev_n) :=
  h.liftTop
    (fun h_sep st => st.receiveNode h_sep h_tail h_lead h_node hjson)
    (fun h_sep st => st.receiveNode h_sep h_tail h_lead h_node hjson)

lemma FlowOpenR.receivePropsEmpty {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end : SurfPos} {ev ev_p : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p) :
    FlowOpenR n Return D ks km (.value false) sp_block sp_end (ev ++ ev_p) :=
  h.receiveNode h_tail h_lead (.propsEmpty _ _ _ _ _ h_props) (fun h => nomatch h)

lemma FlowOpenR.receivePropsContent {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_ne : SurfPos} {ev ev_p ev_c : List Event} {kj : Bool}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_sep : SSeparate n .flowIn sp_end sp_prep)
    (h_content : TFlowContent n .flowIn sp_prep sp_ne ev_c)
    (hjson : kj = true → TCFlowJsonContent n .flowIn sp_prep sp_ne ev_c) :
    FlowOpenR n Return D ks km (.value kj) sp_block sp_ne (ev ++ (ev_p ++ ev_c)) :=
  h.receiveNode h_tail h_lead (.propsContent _ _ _ _ _ _ _ _ h_props h_sep h_content)
    (fun hk => .propsContent _ _ _ _ _ _ _ _ h_props h_sep (hjson hk))

lemma FlowOpenR.receiveQuestion {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : tl = .sep)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (hq : GLit '?' sp_prep sp_tok) :
    FlowOpenR n Return D ks km .question sp_block sp_tok ev := by
  subst h_tail
  exact FlowOpenR.retrace (List.append_nil _) (h.liftTop (delta := [])
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveQuestion h_sep h_lead hq
      exact ⟨a, b, TSeqFrame.retrace (List.append_nil _).symm c⟩)
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveQuestion h_sep h_lead hq
      exact ⟨a, b, TMapFrame.retrace (List.append_nil _).symm c⟩))

lemma FlowOpenR.receiveColonSep {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : tl = .sep)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (hcolon : GLit ':' sp_prep sp_tok) :
    FlowOpenR n Return D ks km (.colon false) sp_block sp_tok ev := by
  subst h_tail
  exact FlowOpenR.retrace (List.append_nil _) (h.liftTop (delta := [])
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonSep h_sep h_lead hcolon
      exact ⟨a, b, TSeqFrame.retrace (List.append_nil _).symm c⟩)
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonSep h_sep h_lead hcolon
      exact ⟨a, b, TMapFrame.retrace (List.append_nil _).symm c⟩))

lemma FlowOpenR.receiveColonQuestion {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (hcolon : GLit ':' sp_prep sp_tok) :
    FlowOpenR n Return D ks km (.colon false) sp_block sp_tok ev := by
  subst h_tail
  exact FlowOpenR.retrace (List.append_nil _) (h.liftTop (delta := [])
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonQuestion h_sep h_lead hcolon
      exact ⟨a, b, TSeqFrame.retrace (List.append_nil _).symm c⟩)
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonQuestion h_sep h_lead hcolon
      exact ⟨a, b, TMapFrame.retrace (List.append_nil _).symm c⟩))

lemma FlowOpenR.receiveColonPropsSep {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : tl = .sep)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep)
    (hcolon : GLit ':' sp_prep sp_tok) :
    FlowOpenR n Return D ks km (.colon false) sp_block sp_tok (ev ++ ev_p) := by
  subst h_tail
  exact h.liftTop
    (fun h_sep st => st.receiveColonPropsSep h_sep h_lead h_props h_gap hcolon)
    (fun h_sep st => st.receiveColonPropsSep h_sep h_lead h_props h_gap hcolon)

lemma FlowOpenR.receiveColonPropsQuestion {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep)
    (hcolon : GLit ':' sp_prep sp_tok) :
    FlowOpenR n Return D ks km (.colon false) sp_block sp_tok (ev ++ ev_p) := by
  subst h_tail
  exact h.liftTop
    (fun h_sep st => st.receiveColonPropsQuestion h_sep h_lead h_props h_gap hcolon)
    (fun h_sep st => st.receiveColonPropsQuestion h_sep h_lead h_props h_gap hcolon)

lemma FlowOpenR.receiveNodeColon {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_ne sp_prep₂ sp_tok : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : tl = .sep ∨ tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n)
    (h_lead₂ : SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne)
    (hcolon : GLit ':' sp_prep₂ sp_tok) :
    FlowOpenR n Return D ks km (.colon kj) sp_block sp_tok (ev ++ ev_n) :=
  h.liftTop
    (fun h_sep st => st.receiveNodeColon h_sep h_tail h_lead
      h_node hjson h_lead₂ hcolon)
    (fun h_sep st => st.receiveNodeColon h_sep h_tail h_lead
      h_node hjson h_lead₂ hcolon)

lemma FlowOpenR.receivePropsNodeColon {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_ne sp_prep₂ sp_tok : SurfPos}
    {ev ev_p ev_c : List Event} {kj : Bool}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev)
    (h_tail : tl = .sep ∨ tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_sep : SSeparate n .flowIn sp_end sp_prep)
    (h_content : TFlowContent n .flowIn sp_prep sp_ne ev_c)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_p sp_ne (ev_p ++ ev_c))
    (h_lead₂ : SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne)
    (hcolon : GLit ':' sp_prep₂ sp_tok) :
    FlowOpenR n Return D ks km (.colon kj) sp_block sp_tok (ev ++ (ev_p ++ ev_c)) :=
  h.receiveNodeColon h_tail h_lead (.propsContent _ _ _ _ _ _ _ _ h_props h_sep h_content) hjson
    h_lead₂ hcolon

lemma FlowOpenR.comma {n D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h : FlowOpenR n Return D ks km tl sp_block sp_flow ev) (h_tail : tl ≠ .sep)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.closeFree = true))
    (hcomma : GLit ',' sp_prep sp_tok) :
    FlowOpenR n Return D ks km .sep sp_block sp_tok ev :=
  FlowOpenR.retrace (List.append_nil _) (h.liftTop (delta := [])
    (fun h_sep st => by
      exact ⟨_, h_sep, TSeqFrame.retrace (List.append_nil _).symm (st.holdCommaLead h_tail h_lead hcomma)⟩)
    (fun h_sep st => by
      exact ⟨_, h_sep, TMapFrame.retrace (List.append_nil _).symm (st.holdCommaLead h_tail h_lead hcomma)⟩))

lemma FlowOpenR.openNestSeq {n d : Nat} {ks km : Array Bool} {b : Bool} {tl_par : FrameTail}
    {sp_block sp_par sp_br sp_open : SurfPos} {ev_par : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
    (h_open : GLit '[' sp_br sp_open) :
    FlowOpenR n Return (d + 1) (ks.push true) (km.push b) .sep sp_block sp_open (ev_par ++ []) :=
  .seqNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_open (.none sp_open) (.betweenEmpty sp_open)

lemma FlowOpenR.openNestMap {n d : Nat} {ks km : Array Bool} {b : Bool} {tl_par : FrameTail}
    {sp_block sp_par sp_br sp_open : SurfPos} {ev_par : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
    (h_open : GLit '{' sp_br sp_open) :
    FlowOpenR n Return (d + 1) (ks.push false) (km.push b) .sep sp_block sp_open (ev_par ++ []) :=
  .mapNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_open (.none sp_open) (.betweenEmpty sp_open)

lemma FlowOpenR.openNestSeqProps {n d : Nat} {ks km : Array Bool} {b : Bool} {tl_par : FrameTail}
    {sp_block sp_par sp_p sp_end sp_br sp_open : SurfPos} {ev_par ev_p : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_psep : SSeparate n .flowIn sp_end sp_br)
    (h_open : GLit '[' sp_br sp_open) :
    FlowOpenR n Return (d + 1) (ks.push true) (km.push b) .sep sp_block sp_open (ev_par ++ (ev_p ++ [])) :=
  .seqNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_props h_psep h_open
    (.none sp_open) (.betweenEmpty sp_open)

lemma FlowOpenR.openNestMapProps {n d : Nat} {ks km : Array Bool} {b : Bool} {tl_par : FrameTail}
    {sp_block sp_par sp_p sp_end sp_br sp_open : SurfPos} {ev_par ev_p : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_b : b = true ↔ ∃ kj, tl_par = .colon kj)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_psep : SSeparate n .flowIn sp_end sp_br)
    (h_open : GLit '{' sp_br sp_open) :
    FlowOpenR n Return (d + 1) (ks.push false) (km.push b) .sep sp_block sp_open (ev_par ++ (ev_p ++ [])) :=
  .mapNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent h_b h_tail h_lead h_props h_psep h_open
    (.none sp_open) (.betweenEmpty sp_open)

lemma FlowOpenR.closeNestedSeq {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_br sp_open sp_es sp_cur sp_prep sp_tok : SurfPos} {ev_par ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
    (h_open : GLit '[' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit ']' sp_prep sp_tok) :
    FlowOpenR n Return d ks km (.value true) sp_block sp_tok (ev_par ++ ev) :=
  have h_seq : TFlowSequence n .flowIn sp_br sp_tok ev :=
    TSeqFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receiveNode h_tail h_lead (.content _ _ _ _ _ (.flowSeq _ _ _ _ _ h_seq))
    (fun _ => .content _ _ _ _ _ (.flowSeq _ _ _ _ _ h_seq))

lemma FlowOpenR.closeNestedMap {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_br sp_open sp_es sp_cur sp_prep sp_tok : SurfPos} {ev_par ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
    (h_open : GLit '{' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit '}' sp_prep sp_tok) :
    FlowOpenR n Return d ks km (.value true) sp_block sp_tok (ev_par ++ ev) :=
  have h_map : TFlowMapping n .flowIn sp_br sp_tok ev :=
    TMapFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receiveNode h_tail h_lead (.content _ _ _ _ _ (.flowMap _ _ _ _ _ h_map))
    (fun _ => .content _ _ _ _ _ (.flowMap _ _ _ _ _ h_map))

lemma FlowOpenR.closeNestedSeqProps {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_p sp_end sp_br sp_open sp_es sp_cur sp_prep sp_tok : SurfPos}
    {ev_par ev_p ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_psep : SSeparate n .flowIn sp_end sp_br)
    (h_open : GLit '[' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit ']' sp_prep sp_tok) :
    FlowOpenR n Return d ks km (.value true) sp_block sp_tok (ev_par ++ (ev_p ++ ev)) :=
  have h_seq : TFlowSequence n .flowIn sp_br sp_tok ev :=
    TSeqFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receivePropsContent h_tail h_lead h_props h_psep (.flowSeq _ _ _ _ _ h_seq)
    (fun _ => .flowSeq _ _ _ _ _ h_seq)

lemma FlowOpenR.closeNestedMapProps {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_p sp_end sp_br sp_open sp_es sp_cur sp_prep sp_tok : SurfPos}
    {ev_par ev_p ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : ∀ kj, tl_par ≠ .value kj)
    (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_psep : SSeparate n .flowIn sp_end sp_br)
    (h_open : GLit '{' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit '}' sp_prep sp_tok) :
    FlowOpenR n Return d ks km (.value true) sp_block sp_tok (ev_par ++ (ev_p ++ ev)) :=
  have h_map : TFlowMapping n .flowIn sp_br sp_tok ev :=
    TMapFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receivePropsContent h_tail h_lead h_props h_psep (.flowMap _ _ _ _ _ h_map)
    (fun _ => .flowMap _ _ _ _ _ h_map)

lemma FlowOpenR.closeNestedSeqColon {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_br sp_open sp_es sp_cur sp_prep sp_tok sp_prep₂ sp_tok₂ : SurfPos}
    {ev_par ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : tl_par = .sep ∨ tl_par = .question)
    (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
    (h_open : GLit '[' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit ']' sp_prep sp_tok)
    (h_lead₃ : SSeparateLines n sp_tok sp_prep₂ ∨ sp_prep₂ = sp_tok)
    (hcolon : GLit ':' sp_prep₂ sp_tok₂) :
    FlowOpenR n Return d ks km (.colon true) sp_block sp_tok₂ (ev_par ++ ev) :=
  have h_seq : TFlowSequence n .flowIn sp_br sp_tok ev :=
    TSeqFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receiveNodeColon h_tail h_lead (.content _ _ _ _ _ (.flowSeq _ _ _ _ _ h_seq))
    (fun _ => .content _ _ _ _ _ (.flowSeq _ _ _ _ _ h_seq)) h_lead₃ hcolon

lemma FlowOpenR.closeNestedMapColon {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_br sp_open sp_es sp_cur sp_prep sp_tok sp_prep₂ sp_tok₂ : SurfPos}
    {ev_par ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : tl_par = .sep ∨ tl_par = .question)
    (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
    (h_open : GLit '{' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit '}' sp_prep sp_tok)
    (h_lead₃ : SSeparateLines n sp_tok sp_prep₂ ∨ sp_prep₂ = sp_tok)
    (hcolon : GLit ':' sp_prep₂ sp_tok₂) :
    FlowOpenR n Return d ks km (.colon true) sp_block sp_tok₂ (ev_par ++ ev) :=
  have h_map : TFlowMapping n .flowIn sp_br sp_tok ev :=
    TMapFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receiveNodeColon h_tail h_lead (.content _ _ _ _ _ (.flowMap _ _ _ _ _ h_map))
    (fun _ => .content _ _ _ _ _ (.flowMap _ _ _ _ _ h_map)) h_lead₃ hcolon

lemma FlowOpenR.closeNestedSeqPropsColon {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_p sp_end sp_br sp_open sp_es sp_cur sp_prep sp_tok sp_prep₂ sp_tok₂ : SurfPos}
    {ev_par ev_p ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : tl_par = .sep ∨ tl_par = .question)
    (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_psep : SSeparate n .flowIn sp_end sp_br)
    (h_open : GLit '[' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit ']' sp_prep sp_tok)
    (h_lead₃ : SSeparateLines n sp_tok sp_prep₂ ∨ sp_prep₂ = sp_tok)
    (hcolon : GLit ':' sp_prep₂ sp_tok₂) :
    FlowOpenR n Return d ks km (.colon true) sp_block sp_tok₂ (ev_par ++ (ev_p ++ ev)) :=
  have h_seq : TFlowSequence n .flowIn sp_br sp_tok ev :=
    TSeqFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receivePropsNodeColon h_tail h_lead h_props h_psep (.flowSeq _ _ _ _ _ h_seq)
    (fun _ => .propsContent _ _ _ _ _ _ _ _ h_props h_psep (.flowSeq _ _ _ _ _ h_seq)) h_lead₃ hcolon

lemma FlowOpenR.closeNestedMapPropsColon {n d : Nat} {ks km : Array Bool} {tl_par tl : FrameTail}
    {sp_block sp_par sp_p sp_end sp_br sp_open sp_es sp_cur sp_prep sp_tok sp_prep₂ sp_tok₂ : SurfPos}
    {ev_par ev_p ev : List Event}
    (parent : FlowOpenR n Return d ks km tl_par sp_block sp_par ev_par)
    (h_tail : tl_par = .sep ∨ tl_par = .question)
    (h_lead : SSeparateLines n sp_par sp_p ∨ (sp_p = sp_par ∧ tl_par.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_psep : SSeparate n .flowIn sp_end sp_br)
    (h_open : GLit '{' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn tl sp_es sp_cur ev)
    (h_lead₂ : SSeparateLines n sp_cur sp_prep ∨ (sp_prep = sp_cur ∧ tl.closeFree = true))
    (h_close : GLit '}' sp_prep sp_tok)
    (h_lead₃ : SSeparateLines n sp_tok sp_prep₂ ∨ sp_prep₂ = sp_tok)
    (hcolon : GLit ':' sp_prep₂ sp_tok₂) :
    FlowOpenR n Return d ks km (.colon true) sp_block sp_tok₂ (ev_par ++ (ev_p ++ ev)) :=
  have h_map : TFlowMapping n .flowIn sp_br sp_tok ev :=
    TMapFrame.closeLead (c_out := .flowIn) h_open h_sep st (h_lead₂.imp (fun h => ⟨h, h⟩) id) h_close
  parent.receivePropsNodeColon h_tail h_lead h_props h_psep (.flowMap _ _ _ _ _ h_map)
    (fun _ => .propsContent _ _ _ _ _ _ _ _ h_props h_psep (.flowMap _ _ _ _ _ h_map)) h_lead₃ hcolon

lemma FlowOpenR.km_size {n d : Nat} {ks km : Array Bool} {tl : FrameTail} {a b : SurfPos}
    {ev : List Event} (h : FlowOpenR n Return d ks km tl a b ev) : km.size = d := by
  induction h <;> simp_all [Array.size_push]

/-- The base closer spends the source-bound return installed by the opener.
No origin is inferred from an unrooted stack or from the closing cursor. -/
lemma FlowOpenR.closeBase {n depth : Nat} {ks km : Array Bool} {tl : FrameTail}
    {outer cur prep stop : SurfPos} {ev : List Event}
    (h : FlowOpenR n Return depth ks km tl outer cur ev)
    (hd : depth = 1) (kind : Bool) (hk : ks = #[kind])
    (lead : SSeparateLines n cur prep ∨ (prep = cur ∧ tl.closeFree = true))
    (close : GLit (if kind then ']' else '}') prep stop) : Return stop ev := by
  subst depth
  cases h with
  | seqBase _ root opened entries _ _ _ ho hs frame returnTo =>
    cases kind
    · simp at hk
    · exact returnTo stop ev (TSeqFrame.closeBase (sp_block := outer) ho hs frame lead close).1
  | mapBase _ root opened entries _ _ _ ho hs frame returnTo =>
    cases kind
    · exact returnTo stop ev (TMapFrame.closeBase (sp_block := outer) ho hs frame lead close).1
    · simp at hk
  | seqNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ => cases parent
  | mapNest _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ => cases parent
  | seqNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ _ _ => cases parent
  | mapNestProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ parent _ _ _ _ _ _ _ _ => cases parent

lemma FlowOpenR.closeSeqBase {n : Nat} {tl : FrameTail}
    {outer cur prep stop : SurfPos} {ev : List Event}
    (h : FlowOpenR n Return 1 #[true] #[false] tl outer cur ev)
    (lead : SSeparateLines n cur prep ∨ (prep = cur ∧ tl.closeFree = true))
    (close : GLit ']' prep stop) : Return stop ev :=
  h.closeBase rfl true rfl lead close

lemma FlowOpenR.closeMapBase {n : Nat} {tl : FrameTail}
    {outer cur prep stop : SurfPos} {ev : List Event}
    (h : FlowOpenR n Return 1 #[false] #[false] tl outer cur ev)
    (lead : SSeparateLines n cur prep ∨ (prep = cur ∧ tl.closeFree = true))
    (close : GLit '}' prep stop) : Return stop ev :=
  h.closeBase rfl false rfl lead close

/-- A completed flow node returns a closable pending document. The event
prior is the actual enclosing stream/document prior, not guessed from a
matching final event. -/
def StreamReturn (start : SurfPos) (prior : List Event) (stop : SurfPos)
    (events : List Event) : Prop :=
  ∀ finish, SSLComments stop finish → TLYamlStream start finish (prior ++ events)

/-- The genuine first-document source prior funds the base return. -/
lemma return_first {start node root : SurfPos}
    (prior : GStar SLDocumentPrefix start node)
    (sep : SSeparate 0 .flowOut node root) :
    ∀ stop events, TFlowContent 0 .flowOut root stop events →
      StreamReturn start [] stop events := by
  intro stop events content finish comments
  simpa using StreamBridge.TLYamlStream.bareRoute prior finish events
    (TBlockNode.flowInBlock 0 .blockIn node root stop finish events sep
      (TFlowNode.content 0 .flowOut root stop events content) comments)

/-- Real document-start source evidence funds the explicit-document return. -/
lemma return_explicit {start block marker node root : SurfPos} {prior : List Event}
    (stream : TLYamlStream start block prior)
    (pre : GStar SLDocumentPrefix block marker)
    (mark : SCDirectivesEnd marker node)
    (sep : SSeparate 0 .flowOut node root) :
    ∀ stop events, TFlowContent 0 .flowOut root stop events →
      StreamReturn start (prior ++ [.beginDocument]) stop events := by
  intro stop events content finish comments
  simpa [List.append_assoc] using TLYamlStream.explicitRoute stream pre mark
    (TAlt.left _ _ _ (TLBareDocument.mk _ _ _
      (TBlockNode.flowInBlock 0 .blockIn node root stop finish events sep
        (TFlowNode.content 0 .flowOut root stop events content) comments)))

/-- Return to the existing pending-content consumer, retaining the real node
end. This is the object consumed by the already qualified document-end step. -/
lemma returned_pending {start block stop : SurfPos} {prior events : List Event}
    (h : StreamReturn start prior stop events) :
    StreamBridge.TPendingNode start false block stop prior events [] :=
  .pendingContent block stop stop prior events h (GStar.nil _)


/-- The live scanner-indexed wrapper. The base return is carried only while a
flow node is open; closing it produces Return at the literal's actual endpoint. -/
inductive FlowStackR (n : Nat) (Return : SurfPos → List Event → Prop) :
    Nat → Array Bool → Array Bool → FrameTail → SurfPos → SurfPos → List Event → Prop where
  | nil (sp : SurfPos) (tl : FrameTail) : FlowStackR n Return 0 #[] #[] tl sp sp []
  | «open» (d : Nat) (ks km : Array Bool) (tl : FrameTail)
      (outer cur : SurfPos) (events : List Event)
      (stack : FlowOpenR n Return (d + 1) ks km tl outer cur events) :
      FlowStackR n Return (d + 1) ks km tl outer cur events

open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PreprocessIndentStable (minContentIndentOf)

lemma gapRead_onR {Return : SurfPos → List Event → Prop} {n d : Nat} {ks km : Array Bool} {sc : L4YAML.Scanner.ScannerState}
    {sp_block sp_flow sp_scan sp_flow₂ : SurfPos} {ev : List Event}
    (hT : FlowOpenR n Return d ks km (tailOf sc.tokens) sp_block sp_flow ev)
    (gap : GapRead sc sp_flow sp_scan sp_flow₂)
    (hn : n ≤ minContentIndentOf sc) :
    ∃ ev_g, FlowOpenR n Return d ks km (gapTail sc) sp_block sp_flow₂ (ev ++ ev_g) := by
  cases gap with
  | white _ h_nil =>
    rw [gapTail_of_nil h_nil]
    exact ⟨[], by simpa using hT⟩
  | props ha ht sp_p h_tail h_lead h_run _ h_held =>
    rw [gapTail_of_held h_held]
    obtain ⟨ev_p, hp⟩ := PropsRun.toT ((h_run n).resolve_right (fun h => h hn))
    exact ⟨ev_p, hT.receivePropsEmpty h_tail ((h_lead n).resolve_right (fun h => h hn)) hp⟩


open L4YAML.Proofs.Serialization.TraceOf.ContentBridge

lemma gapRead_onR_uniform {Return : SurfPos → List Event → Prop} {sc : L4YAML.Scanner.ScannerState} {sp_flow sp_scan sp_flow₂ : SurfPos}
    (gap : L4YAML.Proofs.StreamAccum.GapRead sc sp_flow sp_scan sp_flow₂) :
    ∃ ev_g, ∀ {n d : Nat} {ks km : Array Bool} {sp_block : SurfPos} {ev : List Event},
      n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc →
      FlowOpenR n Return d ks km (tailOf sc.tokens) sp_block sp_flow ev →
      FlowOpenR n Return d ks km (L4YAML.Proofs.StreamAccum.gapTail sc) sp_block sp_flow₂ (ev ++ ev_g) := by
  cases gap with
  | white _ h_nil =>
    rw [L4YAML.Proofs.StreamAccum.gapTail_of_nil h_nil]
    exact ⟨[], fun _ hT => by simpa using hT⟩
  | props ha ht sp_p h_tail h_lead h_run _ h_held =>
    rw [L4YAML.Proofs.StreamAccum.gapTail_of_held h_held]
    obtain ⟨ev_p, hp⟩ := PropsRun.toT ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
    exact ⟨ev_p, fun hn hT =>
      hT.receivePropsEmpty h_tail ((h_lead _).resolve_right (fun h => h hn))
        (TCNsProperties_floor_mono hn hp)⟩


lemma accum_step_flow_return {Return : SurfPos → List Event → Prop} {n : Nat} {sc s' : L4YAML.Scanner.ScannerState} {c : Char}
    {sp_block sp_flow sp_scan sp_block' sp_flow' : SurfPos} {ev : List Event} (km : Array Bool)
    (arm : L4YAML.Proofs.StreamAccum.FlowArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow')
    (hT : FlowStackR n Return sc.flowLevel sc.flowStack km (tailOf sc.tokens) sp_block sp_flow ev)
    (hn : n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc)
    (active : 0 < sc.flowLevel) :
    ∃ ev_g,
      (0 < s'.flowLevel ∧ ∃ km',
        ((c = ',' ∧ km' = km) ∨
          ((c = '[' ∨ c = '{') ∧ ColonKeyCase sc ∧
            ∃ b, km' = km.push b ∧ (b = true ↔ ∃ kj, tailOf sc.tokens = .colon kj)) ∨
          ((c = ']' ∨ c = '}') ∧ km' = km.pop)) ∧
          FlowStackR n Return s'.flowLevel s'.flowStack km' (tailOf s'.tokens) sp_block' sp_flow' (ev ++ ev_g) ∧
          (∀ kj, tailOf s'.tokens = .value kj → (km' = km.pop ∧ km.back? = some true) ∨
            ∀ sp_prep sp_tok, (SSeparateLines n sp_flow' sp_prep ∨ sp_prep = sp_flow') →
              GLit ':' sp_prep sp_tok →
              FlowStackR n Return s'.flowLevel s'.flowStack km' (.colon kj) sp_block' sp_tok (ev ++ ev_g))) ∨
      (s'.flowLevel = 0 ∧ s'.flowStack = #[] ∧ sp_flow' = sp_block' ∧
        ∃ sp_prep sp_tok, ScannerSurfCorr s' sp_tok ∧ GLit c sp_prep sp_tok ∧ Return sp_tok (ev ++ ev_g)) := by
  cases arm with
  | openBase b sp_br sp_open sp_block'' sp_flow'' h_depth h_c h_open h_fl h_ks h_tl h_km h_sp =>
    omega
  | openNest b sp_flow₂ sp_br sp_open gap h_depth h_c h_tail h_klay h_lead h_open h_fl h_ks h_tl =>
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
    have h_ctag : c = '[' ∨ c = '{' := by subst h_c; cases b <;> simp
    cases gap with
    | props ha ht sp_p h_tail₀ h_lead₀ h_run _ h_held =>
      obtain ⟨ev_p, hp₀⟩ := PropsRun.toT ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
      refine ⟨ev_p, Or.inl ⟨by omega, _,
        Or.inr (Or.inl ⟨h_ctag, h_klay, kmBit (tailOf sc.tokens), rfl, kmBit_iff _⟩),
        ?_⟩⟩
      have hp := TCNsProperties_floor_mono hn hp₀
      generalize hks : sc.flowStack = ks at hT
      rw [hd] at hT
      cases hT with
      | «open» _ _ _ _ _ _ _ hTO =>
      have h_lead₀' := (h_lead₀ n).resolve_right (fun h => h hn)
      have h_psep : SSeparate n .flowIn sp_scan sp_br :=
        ((h_lead n).resolve_right (fun h => h hn)).resolve_right (fun h => h_held h.2.2)
      rw [h_fl, h_ks, h_tl, hd, hks]
      refine ⟨?_, fun _ h => nomatch h⟩
      cases b
      · have h_open' : GLit '{' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (FlowOpenR.retrace (by simp)
          (hTO.openNestMapProps (kmBit_iff _) h_tail₀ h_lead₀' hp h_psep h_open'))
      · have h_open' : GLit '[' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (FlowOpenR.retrace (by simp)
          (hTO.openNestSeqProps (kmBit_iff _) h_tail₀ h_lead₀' hp h_psep h_open'))
    | white _ h_nil =>
      refine ⟨[], Or.inl ⟨by omega, _,
        Or.inr (Or.inl ⟨h_ctag, h_klay, kmBit (tailOf sc.tokens), rfl, kmBit_iff _⟩),
        ?_⟩⟩
      generalize hks : sc.flowStack = ks at hT
      rw [hd] at hT
      cases hT with
      | «open» _ _ _ _ _ _ _ hTO =>
      have h_lead' := (h_lead n).resolve_right (fun h => h hn)
      rw [L4YAML.Proofs.StreamAccum.gapTail_of_nil h_nil] at h_lead'
      replace h_lead' := h_lead'.imp id (fun h => And.intro h.1 h.2.1)
      rw [h_fl, h_ks, h_tl, hd, hks]
      refine ⟨?_, fun _ h => nomatch h⟩
      cases b
      · have h_open' : GLit '{' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (hTO.openNestMap (kmBit_iff _) h_tail h_lead' h_open')
      · have h_open' : GLit '[' sp_br sp_flow' := by subst h_c; simpa using h_open
        exact .open _ _ _ _ _ _ _ (hTO.openNestSeq (kmBit_iff _) h_tail h_lead' h_open')
  | comma sp_flow₂ sp_prep sp_tok gap h_depth h_c h_tail h_lead h_lit h_fl h_ks h_tl =>
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 := ⟨sc.flowLevel - 1, by omega⟩
    obtain ⟨ev_g, hG⟩ := gapRead_onR_uniform (Return := Return) gap
    refine ⟨ev_g, Or.inl ⟨by omega, _, Or.inl ⟨h_c, rfl⟩, ?_⟩⟩
    generalize hks : sc.flowStack = ks at hT
    rw [hd] at hT
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
    have h_lead' := (h_lead n).resolve_right (fun h => h hn)
    have hTO₂ := hG hn hTO
    rw [h_fl, h_ks, h_tl, hd, hks]
    exact ⟨.open _ _ _ _ _ _ _ (hTO₂.comma h_tail h_lead' h_lit), fun _ h => nomatch h⟩
  | closeNested b sp_flow₂ sp_prep sp_tok gap h_depth h_c h_top h_lead h_lit h_fl h_ks h_tl =>
    obtain ⟨d, hd⟩ : ∃ d, sc.flowLevel = d + 1 + 1 := ⟨sc.flowLevel - 2, by omega⟩
    have h_ctag : c = ']' ∨ c = '}' := by subst h_c; cases b <;> simp
    obtain ⟨ev_g, hG⟩ := gapRead_onR_uniform (Return := Return) gap
    refine ⟨ev_g, Or.inl ⟨by omega, _, Or.inr (Or.inr ⟨h_ctag, rfl⟩), ?_⟩⟩
    generalize hks : sc.flowStack = ks at hT
    rw [hd] at hT
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
    have h_lead' := (h_lead n).resolve_right (fun h => h hn)
    have hTO₂ := hG hn hTO
    have h_fl' : s'.flowLevel = d + 1 := by omega
    rw [h_fl', h_ks, h_tl, hks]
    rw [hks] at h_top
    generalize hE : ev ++ ev_g = evT at hTO₂ ⊢
    generalize hgt : L4YAML.Proofs.StreamAccum.gapTail sc = tl₂ at hTO₂ h_lead'
    cases hTO₂ with
    | seqNest _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · simp at h_top
      · have h_lit' : GLit ']' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (FlowOpenR.closeNestedSeq parent h_tail_p h_lead_p h_open h_sep st h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (FlowOpenR.closeNestedSeqColon parent ?_ h_lead_p h_open h_sep st h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
    | mapNest _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · have h_lit' : GLit '}' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (FlowOpenR.closeNestedMap parent h_tail_p h_lead_p h_open h_sep st h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (FlowOpenR.closeNestedMapColon parent ?_ h_lead_p h_open h_sep st h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
      · simp at h_top
    | seqNestProps _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_props h_psep h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · simp at h_top
      · have h_lit' : GLit ']' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (FlowOpenR.closeNestedSeqProps parent h_tail_p h_lead_p h_props h_psep h_open h_sep st
            h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (FlowOpenR.closeNestedSeqPropsColon parent ?_ h_lead_p h_props h_psep h_open h_sep st
              h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
    | mapNestProps _ ks₀ km₀ b₀ tl_par _ _ _ _ _ _ _ _ _ _ _ _ parent h_b₀ h_tail_p h_lead_p h_props h_psep h_open h_sep st =>
      rw [Array.back?_push] at h_top
      cases b
      · have h_lit' : GLit '}' sp_prep sp_flow' := by subst h_c; simpa using h_lit
        rw [Array.pop_push, Array.pop_push, Array.back?_push]
        refine ⟨.open _ _ _ _ _ _ _
          (FlowOpenR.closeNestedMapProps parent h_tail_p h_lead_p h_props h_psep h_open h_sep st
            h_lead' h_lit'),
          fun kj hkj => ?_⟩
        cases FrameTail.value.inj hkj
        cases b₀
        · refine Or.inr (fun sp_p sp_t h_l h_col => .open _ _ _ _ _ _ _
            (FlowOpenR.closeNestedMapPropsColon parent ?_ h_lead_p h_props h_psep h_open h_sep st
              h_lead' h_lit' h_l h_col))
          cases tl_par with
          | sep => exact Or.inl rfl
          | question => exact Or.inr rfl
          | colon kj => exact absurd (h_b₀.2 ⟨kj, rfl⟩) Bool.false_ne_true
          | value kj => exact absurd rfl (h_tail_p kj)
        · exact Or.inl ⟨rfl, rfl⟩
      · simp at h_top
  | closeBase b sp_flow₂ sp_prep sp_tok gap h_depth h_c h_top h_lead h_lit h_fl h_ks h_tl h_corr_close =>
    have h_lead' := (h_lead n).resolve_right (fun h => h hn)
    generalize hks : sc.flowStack = ks at hT
    rw [h_depth] at hT
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      obtain ⟨ev_g, hTO₂⟩ := gapRead_onR hTO gap hn
      refine ⟨ev_g, Or.inr ⟨h_fl, h_ks, rfl, sp_prep, sp_tok, h_corr_close, h_lit, ?_⟩⟩
      rw [hks] at h_top
      exact hTO₂.closeBase rfl b h_top h_lead' (by simpa [← h_c] using h_lit)

open L4YAML.CharPredicates
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.NodeProduction L4YAML.Proofs.Acceptance
open L4YAML.Proofs.Serialization.ScannerShape
open L4YAML.Proofs.Serialization.TokenEvents (tokenEvent goOut goOut_append)
open L4YAML.Proofs.Serialization.TraceOf.ContentBridge

lemma accum_step_content_return_in {Return : SurfPos → List Event → Prop} {n D : Nat} {ks km : Array Bool}
    {s_ad s' : ScannerState} {c : Char} {sp_block sp_flow sp_prep sp_a : SurfPos}
    {ev : List Event}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_inflow : s_ad.inFlow = true)
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hcol : s_ad.currentIndent < (s_ad.col : Int))
    (hn : (n : Int) ≤ max 0 (s_ad.currentIndent + 1))
    (hT : FlowOpenR n Return D ks km (tailOf s_ad.tokens) sp_block sp_flow ev)
    (h_tail : ∀ kj, tailOf s_ad.tokens ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨
      (sp_prep = sp_flow ∧ (tailOf s_ad.tokens).leadFree)) :
    ∃ ev_n, PushesTrace s_ad.tokens s'.tokens ev_n ∧
      ((∃ kj sp_ne, tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧
          SFlowNode n .flowIn sp_prep sp_ne ∧
          FlowOpenR n Return D ks km (.value kj) sp_block sp_ne (ev ++ ev_n) ∧
          -- Item 509: the key-then-colon closure (`receiveNodeColon`), where the pre-tail
          -- admits a key — `TFlowStackK`'s T closure is produced here.
          ((tailOf s_ad.tokens = .sep ∨ tailOf s_ad.tokens = .question) →
            ∀ sp_prep₂ sp_tok, (SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne) →
              GLit ':' sp_prep₂ sp_tok →
              FlowOpenR n Return D ks km (.colon kj) sp_block sp_tok (ev ++ ev_n))) ∨
       (tailOf s'.tokens = tailOf s_ad.tokens ∧
         ((c = '&' ∧ TCNsAnchorProperty sp_prep sp_a ev_n) ∨
          (c = '!' ∧ TCNsTagProperty sp_prep sp_a ev_n)))) := by
  obtain ⟨rest, hsp_prep⟩ := peek_some_sp hcorr hpeek
  by_cases hamp : c = '&'
  · subst hamp
    obtain ⟨sp', name, htok, hcorr', hT_anchor⟩ :=
      dispatchContent_anchor_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    have hsp : sp' = sp_a := by
      cases arm with
      | anchor _ h_c _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
      | plain _ _ h_c => exact absurd rfl h_c.1
      | plainIn _ h_c => exact absurd rfl h_c.1
      | doubleQuoted _ h_c => exact absurd h_c (by decide)
      | singleQuoted _ h_c => exact absurd h_c (by decide)
      | blockScalar _ h_c => rcases h_c with h | h <;> exact absurd h (by decide)
      | tag _ h_c => exact absurd h_c (by decide)
      | alias _ h_c => exact absurd h_c (by decide)
    subst hsp
    refine ⟨[.defineAnchor name], ?_, Or.inr ⟨?_, Or.inl ⟨rfl, hT_anchor⟩⟩⟩
    · rw [htok]
      simpa [tokenEvent] using pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .anchor name, s_ad.currentPos⟩ (by simp) (by simp)
    · rw [htok]; exact (tailOf_push_prop (by simp) (by simp [YamlToken.isNodeProperty])).1
  by_cases hbang : c = '!'
  · subst hbang
    obtain ⟨sp', handle, suffix, htok, hcorr', hT_tag⟩ :=
      dispatchContent_tag_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    have hsp : sp' = sp_a := by
      cases arm with
      | tag _ h_c _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
      | plain _ _ h_c => exact absurd rfl h_c.2.2.1
      | plainIn _ h_c => exact absurd rfl h_c.2.2.1
      | doubleQuoted _ h_c => exact absurd h_c (by decide)
      | singleQuoted _ h_c => exact absurd h_c (by decide)
      | blockScalar _ h_c => rcases h_c with h | h <;> exact absurd h (by decide)
      | anchor _ h_c => exact absurd h_c (by decide)
      | alias _ h_c => exact absurd h_c (by decide)
    subst hsp
    refine ⟨_, ?_, Or.inr ⟨?_, Or.inr ⟨rfl, hT_tag⟩⟩⟩
    · rw [htok]
      exact pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .tag handle suffix, s_ad.currentPos⟩ (by simp) (by simp)
    · rw [htok]; exact (tailOf_push_prop (by simp) (by simp [YamlToken.isNodeProperty])).1
  obtain ⟨hpipe, hgt⟩ :=
    Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_inflow h_dispatch
  obtain ⟨⟨kj, h_tl', hkj⟩, -, -⟩ :=
    tailOf_dispatchContent_value h_dispatch hamp hbang hpipe hgt
  by_cases hstar : c = '*'
  · subst hstar
    obtain ⟨sp', name, htok, hcorr', hT_alias⟩ :=
      dispatchContent_alias_trace s_ad sp_prep hcorr hpeek s' h_dispatch
    have hsp : sp' = sp_a := by
      cases arm with
      | alias _ h_c _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
      | plain _ _ h_c => exact absurd rfl h_c.2.1
      | plainIn _ h_c => exact absurd rfl h_c.2.1
      | doubleQuoted _ h_c => exact absurd h_c (by decide)
      | singleQuoted _ h_c => exact absurd h_c (by decide)
      | blockScalar _ h_c => rcases h_c with h | h <;> exact absurd h (by decide)
      | anchor _ h_c => exact absurd h_c (by decide)
      | tag _ h_c => exact absurd h_c (by decide)
    subst hsp
    have hkj0 : kj = false := by
      cases kj with
      | false => rfl
      | true => rcases hkj rfl with h | h <;> exact absurd h (by decide)
    subst hkj0
    refine ⟨[.useAlias name], ?_, Or.inl ⟨false, sp', h_tl', .nil _, .alias _ _ _ _ hT_alias.1, ?_, ?_⟩⟩
    · rw [htok]
      simpa [tokenEvent] using pushesTrace_push s_ad.tokens ⟨s_ad.currentPos, .alias name, s_ad.currentPos⟩ (by simp) (by simp)
    · exact hT.receiveNode h_tail h_lead (.alias _ _ _ _ _ hT_alias) (fun h => nomatch h)
    · intro h_sq sp_p₂ sp_t h_l h_col
      exact hT.receiveNodeColon h_sq h_lead (.alias _ _ _ _ _ hT_alias) (fun h => nomatch h) h_l h_col
  -- The scalar arms: plain, double-quoted, single-quoted.
  obtain ⟨sp_gram, sp', h_node, h_ws, hcorr', -, h_json⟩ :=
    dispatchContent_evidence_flowIn_at n s_ad sp_prep c hcorr hpeek h_inflow h_not_doc h_dispatch hcol hn
  have hsp : sp' = sp_a := by
    cases arm with
    | plain _ _ _ _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | plainIn _ _ _ hcorr_a _ => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | doubleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | singleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | blockScalar _ h_c =>
      rcases h_c with h | h
      · exact absurd h hpipe
      · exact absurd h hgt
    | anchor _ h_c => exact absurd h_c hamp
    | tag _ h_c => exact absurd h_c hbang
    | alias _ h_c => exact absurd h_c hstar
  subst hsp
  have hglue := L4YAML.Proofs.StreamAccum.content_not_glue h_dispatch
  simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
  have hlb : c ≠ '[' := hglue.2.2.1
  have hlc : c ≠ '{' := hglue.2.2.2.2.1
  have hsilent : PushesTrace s_ad.tokens s'.tokens [] := by
    by_cases hdq : c = '"'
    · subst hdq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_doubleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    by_cases hsq : c = '\''
    · subst hsq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_singleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    obtain ⟨str, htok⟩ := dispatchContent_plain_tokens h_dispatch hamp hstar hbang hpipe hgt hdq hsq
    rw [htok]; exact pushesTrace_push_scalar _ _ rfl
  -- The T node and its JSON-ness, once; `receiveNode` lands it, `receiveNodeColon` is the closure.
  have h_tn : TFlowNode n .flowIn sp_prep sp_gram [] ∧
      (kj = true → TCFlowJsonNode n .flowIn sp_prep sp_gram []) := by
    subst hsp_prep
    rcases SFlowNode_head_lift h_node ⟨hamp, hstar, hbang, hlb, hlc⟩ with
      ⟨hdq, hsq, hplain⟩ | ⟨hdq, hq⟩ | ⟨hsq, hq⟩
    · refine ⟨.content _ _ _ _ _ (.plain _ _ _ _ hplain), ?_⟩
      intro hk
      rcases hkj hk with h | h
      · exact absurd h hdq
      · exact absurd h hsq
    · exact ⟨.content _ _ _ _ _ (.doubleQ _ _ _ _ hq), fun _ => .content _ _ _ _ _ (.doubleQ _ _ _ _ hq)⟩
    · exact ⟨.content _ _ _ _ _ (.singleQ _ _ _ _ hq), fun _ => .content _ _ _ _ _ (.singleQ _ _ _ _ hq)⟩
  subst hsp_prep
  exact ⟨[], hsilent, Or.inl ⟨kj, sp_gram, h_tl', h_ws, h_node,
    hT.receiveNode h_tail h_lead h_tn.1 h_tn.2,
    fun h_sq sp_p₂ sp_t h_l h_col => hT.receiveNodeColon h_sq h_lead h_tn.1 h_tn.2 h_l h_col⟩⟩

lemma accum_step_content_return_in_props {Return : SurfPos → List Event → Prop} {n D : Nat} {ks km : Array Bool}
    {s_ad s' : ScannerState} {c : Char} {sp_block sp_flow sp_p sp_e sp_prep sp_a : SurfPos}
    {ev ev_p : List Event}
    (arm : ContentArm s_ad s' c sp_prep sp_a)
    (hcorr : ScannerSurfCorr s_ad sp_prep) (hpeek : s_ad.peek? = some c)
    (h_inflow : s_ad.inFlow = true)
    (h_not_doc : s_ad.col = 0 → atDocumentBoundary s_ad = false)
    (h_dispatch : scanNextToken_dispatchContent s_ad c = .ok s')
    (hcol : s_ad.currentIndent < (s_ad.col : Int))
    (hn : (n : Int) ≤ max 0 (s_ad.currentIndent + 1))
    (hT : FlowOpenR n Return D ks km (tailOf s_ad.tokens) sp_block sp_flow ev)
    (h_tail : ∀ kj, tailOf s_ad.tokens ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_p ∨
      (sp_p = sp_flow ∧ (tailOf s_ad.tokens).leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_e ev_p)
    (h_sep : SSeparate n .flowIn sp_e sp_prep)
    (h_val : c ≠ '&' ∧ c ≠ '!' ∧ c ≠ '*') :
    ∃ kj sp_ne, PushesTrace s_ad.tokens s'.tokens [] ∧
      tailOf s'.tokens = .value kj ∧ GStar SSWhite sp_ne sp_a ∧ SFlowNode n .flowIn sp_prep sp_ne ∧
      FlowOpenR n Return D ks km (.value kj) sp_block sp_ne (ev ++ (ev_p ++ [])) ∧
      -- Item 509: the decorated key's closure (`receivePropsNodeColon`).
      ((tailOf s_ad.tokens = .sep ∨ tailOf s_ad.tokens = .question) →
        ∀ sp_prep₂ sp_tok, (SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne) →
          GLit ':' sp_prep₂ sp_tok →
          FlowOpenR n Return D ks km (.colon kj) sp_block sp_tok (ev ++ (ev_p ++ []))) := by
  obtain ⟨hamp, hbang, hstar⟩ := h_val
  obtain ⟨rest, hsp_prep⟩ := peek_some_sp hcorr hpeek
  obtain ⟨hpipe, hgt⟩ :=
    Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_inflow h_dispatch
  obtain ⟨⟨kj, h_tl', hkj⟩, -, -⟩ :=
    tailOf_dispatchContent_value h_dispatch hamp hbang hpipe hgt
  obtain ⟨sp_gram, sp', h_node, h_ws, hcorr', -, -⟩ :=
    dispatchContent_evidence_flowIn_at n s_ad sp_prep c hcorr hpeek h_inflow h_not_doc h_dispatch hcol hn
  have hsp : sp' = sp_a := by
    cases arm with
    | plain _ _ _ _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | plainIn _ _ _ hcorr_a _ => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | doubleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | singleQuoted _ _ _ _ hcorr_a => exact ScannerSurfCorr_unique hcorr' hcorr_a
    | blockScalar _ h_c =>
      rcases h_c with h | h
      · exact absurd h hpipe
      · exact absurd h hgt
    | anchor _ h_c => exact absurd h_c hamp
    | tag _ h_c => exact absurd h_c hbang
    | alias _ h_c => exact absurd h_c hstar
  subst hsp
  have hglue := L4YAML.Proofs.StreamAccum.content_not_glue h_dispatch
  simp only [isFlowIndicatorBool, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.mem_cons, List.mem_nil_iff, or_false, not_or] at hglue
  have hlb : c ≠ '[' := hglue.2.2.1
  have hlc : c ≠ '{' := hglue.2.2.2.2.1
  have hsilent : PushesTrace s_ad.tokens s'.tokens [] := by
    by_cases hdq : c = '"'
    · subst hdq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_doubleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    by_cases hsq : c = '\''
    · subst hsq
      obtain ⟨_, v, htok, -, -⟩ :=
        dispatchContent_singleQuoted_trace s_ad sp_prep hcorr hpeek s' h_dispatch
      rw [htok]; exact pushesTrace_push_scalar _ _ rfl
    obtain ⟨str, htok⟩ := dispatchContent_plain_tokens h_dispatch hamp hstar hbang hpipe hgt hdq hsq
    rw [htok]; exact pushesTrace_push_scalar _ _ rfl
  have h_tc : TFlowContent n .flowIn sp_prep sp_gram [] ∧
      (kj = true → TCFlowJsonContent n .flowIn sp_prep sp_gram []) := by
    subst hsp_prep
    rcases SFlowNode_head_lift h_node ⟨hamp, hstar, hbang, hlb, hlc⟩ with
      ⟨hdq, hsq, hplain⟩ | ⟨hdq, hq⟩ | ⟨hsq, hq⟩
    · refine ⟨.plain _ _ _ _ hplain, ?_⟩
      intro hk
      rcases hkj hk with h | h
      · exact absurd h hdq
      · exact absurd h hsq
    · exact ⟨.doubleQ _ _ _ _ hq, fun _ => .doubleQ _ _ _ _ hq⟩
    · exact ⟨.singleQ _ _ _ _ hq, fun _ => .singleQ _ _ _ _ hq⟩
  subst hsp_prep
  exact ⟨kj, sp_gram, hsilent, h_tl', h_ws, h_node,
    hT.receivePropsContent h_tail h_lead h_props h_sep h_tc.1 h_tc.2,
    fun h_sq sp_p₂ sp_t h_l h_col => hT.receivePropsNodeColon h_sq h_lead h_props h_sep h_tc.1
      (fun hk => .propsContent _ _ _ _ _ _ _ _ h_props h_sep (h_tc.2 hk)) h_l h_col⟩


lemma accum_step_key_return {Return : SurfPos → List Event → Prop} {d : Nat} {sc s' : ScannerState} {c : Char}
    {sp_block sp_flow sp_scan sp_block' sp_flow' : SurfPos} {ks km : Array Bool} {ev : List Event}
    (arm : L4YAML.Proofs.StreamAccum.KeyArm sc s' c sp_block sp_flow sp_scan sp_block' sp_flow') :
    ∃ ev_g, ∀ n, n ≤ minContentIndentOf sc →
      FlowStackR n Return (d + 1) ks km (tailOf sc.tokens) sp_block sp_flow ev →
      (∀ kj, tailOf sc.tokens = .value kj →
        L4YAML.Proofs.EntryBoundaryLayout.KeyAfterValueLayout sc ∨
        ∀ sp_prep sp_tok, (SSeparateLines n sp_flow sp_prep ∨ sp_prep = sp_flow) →
          GLit ':' sp_prep sp_tok → FlowStackR n Return (d + 1) ks km (.colon kj) sp_block sp_tok ev) →
      FlowStackR n Return (d + 1) ks km (tailOf s'.tokens) sp_block' sp_flow' (ev ++ ev_g) := by
  cases arm with
  | question sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT _ => ?_⟩
    rw [List.append_nil, h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      exact .open _ _ _ _ _ _ _ (hTO.receiveQuestion h_tail
        (((h_lead n).resolve_right (fun h => h hn)).imp id (fun h => ⟨h, by rw [h_tail]; rfl⟩)) h_lit)
  | colonValue kj sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_layout h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT hcl => ?_⟩
    rw [List.append_nil, h_tl]
    exact ((hcl kj h_tail).resolve_left h_layout) _ _
      ((h_lead n).resolve_right (fun h => h hn)) h_lit
  | colonSep sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT _ => ?_⟩
    rw [List.append_nil, h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonSep h_tail
        (((h_lead n).resolve_right (fun h => h hn)).imp id (fun h => ⟨h, by rw [h_tail]; rfl⟩)) h_lit)
  | colonQuestion sp_prep sp_tok h_c h_tail h_run h_lead h_lit h_fl h_ks h_tl =>
    refine ⟨[], fun n hn hT _ => ?_⟩
    rw [List.append_nil, h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonQuestion h_tail
        (Or.inl ((h_lead n).resolve_right (fun h => h hn))) h_lit)
  | colonPropsSep ha ht sp_p sp_prep sp_tok h_c h_tail h_held h_lead h_run h_sep h_lit h_fl h_ks h_tl =>
    obtain ⟨ev_p, hp₀⟩ :=
      L4YAML.Proofs.Serialization.TraceOf.FlowWalk.PropsRun.toT
        ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
    refine ⟨ev_p, fun n hn hT _ => ?_⟩
    rw [h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      have hp := TCNsProperties_floor_mono hn hp₀
      have h_gap : GOpt (SSeparate n .flowIn) sp_scan sp_prep := by
        rcases (h_sep n).resolve_right (fun h => h hn) with hs | hs
        · exact GOpt.some _ _ hs
        · cases hs; exact GOpt.none _
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonPropsSep h_tail
        ((h_lead n).resolve_right (fun h => h hn)) hp h_gap h_lit)
  | colonPropsQuestion ha ht sp_p sp_prep sp_tok h_c h_tail h_held h_lead h_run h_sep h_lit h_fl h_ks h_tl =>
    obtain ⟨ev_p, hp₀⟩ :=
      L4YAML.Proofs.Serialization.TraceOf.FlowWalk.PropsRun.toT
        ((h_run _).resolve_right (fun h => h (Nat.le_refl _)))
    refine ⟨ev_p, fun n hn hT _ => ?_⟩
    rw [h_tl]
    cases hT with
    | «open» _ _ _ _ _ _ _ hTO =>
      have hp := TCNsProperties_floor_mono hn hp₀
      have h_gap : GOpt (SSeparate n .flowIn) sp_scan sp_prep := by
        rcases (h_sep n).resolve_right (fun h => h hn) with hs | hs
        · exact GOpt.some _ _ hs
        · cases hs; exact GOpt.none _
      exact .open _ _ _ _ _ _ _ (hTO.receiveColonPropsQuestion h_tail
        ((h_lead n).resolve_right (fun h => h hn)) hp h_gap h_lit)

/-- The real preprocessing/content dispatch preserves the funded return.
This reuses the existing InteriorGap/ContentLead calculation. -/
lemma accum_step_content_returnK {Return : SurfPos → List Event → Prop} {n d : Nat} {km : Array Bool} {sc s_prep s' : ScannerState} {c : Char}
    {sp_block sp_flow sp_scan : SurfPos} {ev : List Event}
    (hd : sc.flowLevel = d + 1)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_str_none : scanNextToken_dispatchStructural s_prep c = .ok none)
    (h_flow_none : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    (h_blk_none : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok none)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    (h_not_doc : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).col = 0 →
      atDocumentBoundary (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) = false)
    (h_gap : L4YAML.Proofs.StreamAccum.InteriorGap sc (tailOf sc.tokens) sp_flow sp_scan)
    (h_real : L4YAML.Proofs.FlowAdjacency.LastTokenReal sc.tokens)
    (hT : FlowStackR n Return sc.flowLevel sc.flowStack km (tailOf sc.tokens) sp_block sp_flow ev)
    (hn : n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc) :
    ∃ ev_n sp_prep sp_a,
      ScannerSurfCorr (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) sp_prep ∧
      ContentArm (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) s' c sp_prep sp_a ∧
      ((∃ kj sp_ne, tailOf s'.tokens = .value kj ∧ (c ≠ '&' ∧ c ≠ '!') ∧ GStar SSWhite sp_ne sp_a ∧
          SFlowNode n .flowIn sp_prep sp_ne ∧
          FlowStackR n Return s'.flowLevel s'.flowStack km (tailOf s'.tokens) sp_block sp_ne (ev ++ ev_n)) ∨
       (tailOf s'.tokens = tailOf sc.tokens ∧ (c = '&' ∨ c = '!') ∧
          FlowStackR n Return s'.flowLevel s'.flowStack km (tailOf s'.tokens) sp_block sp_flow ev)) := by
  -- The dispatch state and its projections.
  generalize h_ad_def : (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) = s_ad at h_flow_none h_blk_none h_dispatch h_not_doc ⊢
  have h_ad_tokens : s_ad.tokens = s_prep.tokens := by rw [← h_ad_def]; split <;> rfl
  have h_ad_peek : s_ad.peek? = s_prep.peek? := by rw [← h_ad_def]; split <;> rfl
  have h_ad_fl : s_ad.flowLevel = s_prep.flowLevel := by rw [← h_ad_def]; split <;> rfl
  have h_ad_fs : s_ad.flowStack = s_prep.flowStack := by rw [← h_ad_def]; split <;> rfl
  have h_ad_ind : s_ad.indents = s_prep.indents := by rw [← h_ad_def]; split <;> rfl
  have h_ad_col : s_ad.col = s_prep.col := by rw [← h_ad_def]; split <;> rfl
  have h_sc_inflow : sc.inFlow = true := L4YAML.Proofs.StreamAccum.inFlow_of_flowLevel_eq hd
  have h_prep_fl : s_prep.flowLevel = sc.flowLevel :=
    L4YAML.Proofs.FlowSync.preprocess_preserves_flowLevel sc s_prep c h_preprocess
  have h_prep_fs : s_prep.flowStack = sc.flowStack :=
    L4YAML.Proofs.ScannerFlowStack.preprocess_preserves_flowStack sc s_prep c h_preprocess
  have h_prep_ind : s_prep.indents = sc.indents :=
    L4YAML.Proofs.FlowIndentStable.preprocess_indents_of_inFlow h_sc_inflow h_preprocess
  have h_prep_inflow : s_prep.inFlow = true := by
    unfold ScannerState.inFlow; rw [h_prep_fl, hd]; simp
  have h_ad_inflow : s_ad.inFlow = true := by
    unfold ScannerState.inFlow; rw [h_ad_fl, h_prep_fl, hd]; simp
  have hpeek : s_ad.peek? = some c :=
    h_ad_peek.trans (L4YAML.Proofs.StreamAccum.preprocess_some_peek h_preprocess)
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    L4YAML.Proofs.ScanStrictCoupling.scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  have hcorr_ad : ScannerSurfCorr s_ad sp_prep := by
    rw [← h_ad_def]; exact L4YAML.Proofs.StreamAccum.corr_of_allowDirectives_update hcorr_prep
  have hcol : s_ad.currentIndent < (s_ad.col : Int) := by
    rw [h_ad_col, L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq h_ad_ind]
    exact L4YAML.Proofs.FlowIndentStable.structural_none_col_gt_of_inFlow h_prep_inflow h_str_none
  have hn' : (n : Int) ≤ max 0 (s_ad.currentIndent + 1) := by
    rw [L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq (h_ad_ind.trans h_prep_ind)]
    unfold L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf at hn
    omega
  have h_tl_eq : tailOf s_ad.tokens = tailOf sc.tokens :=
    tailOf_preprocess_eq (by omega) h_preprocess h_ad_tokens
  -- The post-state's flow indices are the pre-state's.
  have h_fl' : s'.flowLevel = sc.flowLevel :=
    (L4YAML.Proofs.ScannerCorrectness.dispatchContent_preserves_flowLevel s_ad c s' h_dispatch).trans
      (h_ad_fl.trans h_prep_fl)
  have h_fs' : s'.flowStack = sc.flowStack :=
    (L4YAML.Proofs.ScannerFlowStack.dispatchContent_preserves_flowStack s_ad c s' h_dispatch).trans
      (h_ad_fs.trans h_prep_fs)
  obtain ⟨sp_a, arm⟩ :=
    L4YAML.Proofs.StreamAccum.contentArm_of_dispatch s_ad sp_prep c hcorr_ad hpeek h_not_doc (fun _ => hcol) h_dispatch
  have h_lead := contentLead_of_interior hd h_corr hcorr_prep h_preprocess h_str_none h_ad_tokens
    h_ad_fl h_flow_none h_blk_none h_dispatch h_gap h_real
  -- The T stack at depth ≥ 1 is open.
  rw [hd] at hT
  rcases hT with _ | ⟨_, _, _, _, _, _, _, h_fos⟩
  rw [h_fl', h_fs', hd]
  have h_fos' := h_fos
  rw [← h_tl_eq] at h_fos'
  by_cases hprop : c = '&' ∨ c = '!'
  · -- Property arms keep the tail and the trace.
    have h_kept := content_prop_tail_kept hcorr_ad hpeek h_dispatch hprop
    refine ⟨[], sp_prep, sp_a, hcorr_ad, arm, Or.inr ⟨h_kept.trans h_tl_eq, hprop, ?_⟩⟩
    rw [h_kept]; exact .«open» _ _ _ _ _ _ _ h_fos'
  · have hamp : c ≠ '&' := fun h => hprop (Or.inl h)
    have hbang : c ≠ '!' := fun h => hprop (Or.inr h)
    cases h_lead with
    | white h_tail h_lead =>
      obtain ⟨ev_n, -, h | ⟨-, h⟩⟩ := accum_step_content_return_in arm hcorr_ad hpeek h_ad_inflow h_not_doc
        h_dispatch hcol hn' h_fos' (by rw [h_tl_eq]; exact h_tail)
        (by rw [h_tl_eq]; exact h_lead n hn)
      · obtain ⟨kj, sp_ne, h_tl', h_ws, h_nd, h_open, -⟩ := h
        exact ⟨ev_n, sp_prep, sp_a, hcorr_ad, arm, Or.inl ⟨kj, sp_ne, h_tl', ⟨hamp, hbang⟩, h_ws, h_nd, by
          rw [h_tl']; exact .«open» _ _ _ _ _ _ _ h_open⟩⟩
      · rcases h with ⟨hc, -⟩ | ⟨hc, -⟩
        · exact absurd hc hamp
        · exact absurd hc hbang
    | props ha ht sp_p sp_e h_tail h_lead_p h_run h_sep h_last_sc =>
      have hstar : c ≠ '*' := by
        intro hc; subst hc
        have h_false := L4YAML.Proofs.StreamAccum.lastTokenIsNodeProperty_false_of_dispatch h_dispatch
        obtain ⟨t, h_last, h_prop⟩ := h_last_sc
        have h_ad_last : L4YAML.Scanner.lastRealTokenVal? s_ad.tokens =
            L4YAML.Scanner.lastRealTokenVal? sc.tokens := by
          rw [h_ad_tokens]
          exact L4YAML.Proofs.StreamAccum.preprocess_preserves_lastRealTokenVal_inFlow sc s_prep _
            (by omega) h_real h_preprocess
        unfold lastTokenIsNodeProperty at h_false
        rw [h_ad_inflow, h_ad_last, h_last] at h_false
        simp [h_prop] at h_false
      obtain ⟨ev_p, h_props⟩ := L4YAML.Proofs.Serialization.TraceOf.FlowWalk.PropsRun.toT (h_run n hn)
      obtain ⟨kj, sp_ne, -, h_tl', h_ws, h_nd, h_open, -⟩ := accum_step_content_return_in_props arm hcorr_ad hpeek
        h_ad_inflow h_not_doc h_dispatch hcol hn' h_fos' (by rw [h_tl_eq]; exact h_tail)
        (by rw [h_tl_eq]; exact h_lead_p n hn) h_props (h_sep n hn) ⟨hamp, hbang, hstar⟩
      exact ⟨ev_p ++ [], sp_prep, sp_a, hcorr_ad, arm, Or.inl ⟨kj, sp_ne, h_tl', ⟨hamp, hbang⟩, h_ws, h_nd, by
        rw [h_tl']; exact .«open» _ _ _ _ _ _ _ h_open⟩⟩



/-- Spend a funded base return at the very same source cursor returned by
accum_step_flow. Both native close arms supply that cursor correspondence.
The existing S pending park can therefore retain its actual indices. -/
lemma base_close_pending {n : Nat} {sc after : ScannerState} {c : Char}
    {start outer flow scan outer' flow' scan' : SurfPos}
    {prior events : List Event} (mask : Array Bool)
    (arm : FlowArm sc after c outer flow scan outer' flow')
    (stack : FlowStackR n (StreamReturn start prior) sc.flowLevel sc.flowStack
      mask (tailOf sc.tokens) outer flow events)
    (floor : n ≤ minContentIndentOf sc)
    (active : 0 < sc.flowLevel) (closed : after.flowLevel = 0)
    (corr : ScannerSurfCorr after scan') :
    ∃ gapEvents, StreamBridge.TPendingNode start false flow' scan'
      prior (events ++ gapEvents) [] := by
  obtain ⟨gapEvents, h⟩ := accum_step_flow_return mask arm stack floor active
  rcases h with ⟨h_live, _⟩ | ⟨_, _, h_boundary, prep, stop, h_corr, _, h_return⟩
  · omega
  · have h_stop : stop = scan' := ScannerSurfCorr_unique h_corr corr
    subst stop
    rw [h_boundary]
    exact ⟨gapEvents, returned_pending h_return⟩

end L4YAML.Proofs.Serialization.TraceOf.FlowReturn
end Blanket
