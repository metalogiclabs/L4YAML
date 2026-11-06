import Lean
import L4YAML.Init

/-!
# Sidecar: same-column sequence/map continuation ordering

Source target: nasa-jpl/L4YAML 64795a8db28ccfdae85082c93b6453001ae9d3e4.
This isolated experiment models the exact two fields of `FrameLevel` and the
strict width requirement of `KeyFrames.level`; the only L4YAML import is its
prelude (for the repository's `lemma` syntax), not a grammar/scanner theorem.
It is NOT a proof of scanner preservation or of `parse_iff_grammar`.

Status at preparation: CANDIDATE, NOT YET COMPILED. A successful CI run and
axiom inspection are required before promoting even this algebraic result.

The semantic case is `a:\n- b\n- c\nd: 1`: a sequence at width zero inside a
mapping at width zero.  Source item 389 represents the outer map continuation
as an extra conjunct because strict widths keep it out of the mixed frame list.
Source item 392's uniform `<` to `≤` experiment is NOT proposed here: it allowed
duplicate mapping widths and broke the meaning of `ResumeWidths`.
-/

namespace FrameOrderAudit

structure Frame where
  width : Nat
  isSeq : Bool
deriving DecidableEq, Repr

abbrev mapFrame (n : Nat) : Frame := ⟨n, false⟩
abbrev seqFrame (n : Nat) : Frame := ⟨n, true⟩

/-- Executable form of the old `∀ fr ∈ ks, fr.width < k` constructor premise. -/
def oldAdmits : List Frame → Bool
  | [] => true
  | f :: fs => fs.all (fun e => e.width < f.width) && oldAdmits fs

-- The existing width-only discipline cannot admit this mixed, same-column stack.
#guard !oldAdmits [seqFrame 0, mapFrame 0]

/-- Maps precede sequences at the same column; narrower columns precede both. -/
def rank (f : Frame) : Nat := 2 * f.width + if f.isSeq then 1 else 0

lemma rank_exact (outer inner : Frame) :
    rank outer < rank inner ↔ outer.width < inner.width ∨
      (outer.width = inner.width ∧ outer.isSeq = false ∧ inner.isSeq = true) := by
  rcases outer with ⟨a, sa⟩
  rcases inner with ⟨b, sb⟩
  cases sa <;> cases sb <;> simp [rank] <;> omega

lemma old_order_embeds {outer inner : Frame} (h : outer.width < inner.width) :
    rank outer < rank inner := (rank_exact outer inner).mpr (Or.inl h)

lemma rank_injective {a b : Frame} (h : rank a = rank b) : a = b := by
  rcases a with ⟨a, sa⟩
  rcases b with ⟨b, sb⟩
  cases sa <;> cases sb <;> simp [rank] at h <;>
    first | (have hab : a = b := by omega; subst hab; rfl) | omega

lemma rank_wellFounded : WellFounded (fun a b : Frame => rank a < rank b) :=
  InvImage.wf rank Nat.lt_wfRel.wf

/-- All existing mapping-landings retain the EXACT old survivor criterion. -/
lemma below_map_iff (f : Frame) (n : Nat) :
    rank f < rank (mapFrame n) ↔ f.width < n := by
  rcases f with ⟨w, s⟩
  cases s <;> simp [rank] <;> omega

/-- Only sequence-landings change: their same-column outer map survives. -/
lemma below_seq_iff (f : Frame) (n : Nat) :
    rank f < rank (seqFrame n) ↔ f.width < n ∨ f = mapFrame n := by
  rcases f with ⟨w, s⟩
  cases s <;> simp [rank] <;> omega

def rankAdmits : List Frame → Bool
  | [] => true
  | f :: fs => fs.all (fun e => rank e < rank f) && rankAdmits fs

#guard rankAdmits [seqFrame 0, mapFrame 0]
#guard rankAdmits [seqFrame 2, mapFrame 2, seqFrame 0, mapFrame 0]
#guard !rankAdmits [mapFrame 0, seqFrame 0]
#guard !rankAdmits [mapFrame 0, mapFrame 0]
#guard !rankAdmits [seqFrame 0, seqFrame 0]

-- This is the failed item-392 direction, retained as a negative control.
def looseAdmits : List Frame → Bool
  | [] => true
  | f :: fs => fs.all (fun e => e.width ≤ f.width) && looseAdmits fs

#guard looseAdmits [mapFrame 0, mapFrame 0]
#guard !rankAdmits [mapFrame 0, mapFrame 0]

variable {α : Type}

/-- The old mixed `KeyFrames` algebra, with surface tails left abstract. -/
inductive OldFrames (Tail : Frame → α → α → Prop) (P : α → Prop) :
    List Frame → α → Prop where
  | bottom (a : α) (h : P a) : OldFrames Tail P [] a
  | level (e : Frame) (ks : List Frame) (a : α)
      (h_lt : ∀ f ∈ ks, f.width < e.width)
      (h_cont : ∀ b, Tail e a b → OldFrames Tail P ks b) :
      OldFrames Tail P (e :: ks) a

/-- Candidate representation: same tail obligations, finer ordering only. -/
inductive Frames (Tail : Frame → α → α → Prop) (P : α → Prop) :
    List Frame → α → Prop where
  | bottom (a : α) (h : P a) : Frames Tail P [] a
  | level (e : Frame) (ks : List Frame) (a : α)
      (h_lt : ∀ f ∈ ks, rank f < rank e)
      (h_cont : ∀ b, Tail e a b → Frames Tail P ks b) :
      Frames Tail P (e :: ks) a

variable {Tail : Frame → α → α → Prop} {P : α → Prop}

lemma old_same_column_impossible {n : Nat} {ks : List Frame} {a : α} :
    ¬ OldFrames Tail P (seqFrame n :: mapFrame n :: ks) a := by
  intro h
  cases h with
  | level _ _ _ h_lt _ =>
    exact Nat.lt_irrefl n (h_lt (mapFrame n) (by simp))

lemma Frames.ofOld : ∀ {ks : List Frame} {a : α},
    OldFrames Tail P ks a → Frames Tail P ks a
  | [], _, h => by cases h with | bottom a hp => exact .bottom a hp
  | _ :: _, _, h => by
      cases h with
      | level e ks a h_lt h_cont =>
        exact .level e ks a (fun f hf => old_order_embeds (h_lt f hf))
          (fun b ht => Frames.ofOld (h_cont b ht))

lemma Frames.close (tail_nil : ∀ e a, Tail e a a) :
    ∀ {ks : List Frame} {a : α}, Frames Tail P ks a → P a
  | [], _, h => by cases h with | bottom _ hp => exact hp
  | e :: _, a, h => by
      cases h with
      | level _ _ _ _ h_cont =>
        exact Frames.close tail_nil (h_cont a (tail_nil e a))

lemma Frames.level_inv {e : Frame} {ks : List Frame} {a : α}
    (h : Frames Tail P (e :: ks) a) :
    ∀ b, Tail e a b → Frames Tail P ks b := by
  cases h with | level _ _ _ _ h_cont => exact h_cont

lemma Frames.ordered (tail_nil : ∀ e a, Tail e a a) :
    ∀ {ks : List Frame} {a : α}, Frames Tail P ks a →
      ks.Pairwise (fun inner outer => rank outer < rank inner)
  | [], _, _ => .nil
  | e :: _, a, h => by
      cases h with
      | level _ _ _ h_lt h_cont =>
        exact .cons h_lt (Frames.ordered tail_nil (h_cont a (tail_nil e a)))

lemma Frames.nodup (tail_nil : ∀ e a, Tail e a a)
    {ks : List Frame} {a : α} (h : Frames Tail P ks a) : ks.Nodup := by
  apply (Frames.ordered tail_nil h).imp
  intro e f hlt heq
  subst heq
  exact Nat.lt_irrefl _ hlt

/-- Exact survivors, including the full level kind; neither direction omitted. -/
def Survivors (ks ks' : List Frame) (e : Frame) : Prop :=
  ∀ f, f ∈ ks' ↔ f ∈ ks ∧ rank f < rank e

lemma Survivors.map_iff {ks ks' : List Frame} {n : Nat} :
    Survivors ks ks' (mapFrame n) ↔
      (∀ f, f ∈ ks' ↔ f ∈ ks ∧ f.width < n) := by
  simp only [Survivors, below_map_iff]

/-- The exact analogue of `KeyFrames.resumeAt`, not just a survivor bound. -/
lemma Frames.resumeAt (tail_nil : ∀ e a, Tail e a a) {a : α} :
    ∀ {ks : List Frame}, Frames Tail P ks a → ∀ {e : Frame}, e ∈ ks →
      ∃ ks', Survivors ks ks' e ∧
        (∀ b, Tail e a b → Frames Tail P ks' b)
  | [], _, _, hmem => absurd hmem (List.not_mem_nil)
  | k :: ks, h, e, hmem => by
      cases h with
      | level _ _ _ h_lt h_cont =>
        by_cases he : e = k
        · subst he
          refine ⟨ks, fun f => ⟨fun hf =>
            ⟨List.mem_cons_of_mem _ hf, h_lt f hf⟩, ?_⟩, h_cont⟩
          rintro ⟨hm, hlt⟩
          rcases List.mem_cons.mp hm with rfl | hf
          · exact absurd hlt (Nat.lt_irrefl _)
          · exact hf
        · have hmem' : e ∈ ks :=
            (List.mem_cons.mp hmem).elim (fun h => absurd h he) id
          obtain ⟨ks', h_surv, cont⟩ :=
            Frames.resumeAt tail_nil (h_cont a (tail_nil k a)) hmem'
          refine ⟨ks', fun f => ⟨fun hf =>
            ⟨List.mem_cons_of_mem _ ((h_surv f).mp hf).1,
              ((h_surv f).mp hf).2⟩, ?_⟩, cont⟩
          rintro ⟨hm, hlt⟩
          rcases List.mem_cons.mp hm with rfl | hf
          · exact absurd (Nat.lt_trans (h_lt e hmem') hlt) (Nat.lt_irrefl _)
          · exact (h_surv f).mpr ⟨hf, hlt⟩

/-- The already-real item-389 sequence→map continuation is packaged with NO
weaker bottom and NO alternative `True`.  This equivalence is independent of
which surface grammar tail relations instantiate `Tail`. -/
lemma same_column_pack_iff {n : Nat} {ks : List Frame} {a : α}
    (h_lt : ∀ f ∈ ks, f.width < n) :
    Frames Tail P (seqFrame n :: mapFrame n :: ks) a ↔
      (∀ b, Tail (seqFrame n) a b →
        ∀ c, Tail (mapFrame n) b c → Frames Tail P ks c) := by
  constructor
  · intro h b hb c hc
    exact (h.level_inv b hb).level_inv c hc
  · intro h
    refine .level (seqFrame n) (mapFrame n :: ks) a ?_ ?_
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simp [rank]
      · exact old_order_embeds (h_lt f hf)
    · intro b hb
      exact .level (mapFrame n) ks b
        (fun f hf => old_order_embeds (h_lt f hf)) (h b hb)

lemma same_column_old_base {n : Nat} {ks : List Frame} {a : α}
    (h_lt : ∀ f ∈ ks, f.width < n)
    (h : ∀ b, Tail (seqFrame n) a b →
      ∀ c, Tail (mapFrame n) b c → OldFrames Tail P ks c) :
    Frames Tail P (seqFrame n :: mapFrame n :: ks) a :=
  (same_column_pack_iff h_lt).mpr (fun b hb c hc => Frames.ofOld (h b hb c hc))

#print axioms rank_exact
#print axioms rank_injective
#print axioms rank_wellFounded
#print axioms below_map_iff
#print axioms below_seq_iff
#print axioms old_same_column_impossible
#print axioms Frames.ofOld
#print axioms Frames.close
#print axioms Frames.nodup
#print axioms Frames.resumeAt
#print axioms same_column_pack_iff
#print axioms same_column_old_base

end FrameOrderAudit
