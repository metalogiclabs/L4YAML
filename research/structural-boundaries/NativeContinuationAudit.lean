import L4YAML.Proofs.Production.StreamAccum

/-!
# Native item-389 continuation normalization

Target: nasa-jpl/L4YAML 64795a8db28ccfdae85082c93b6453001ae9d3e4.
Status at preparation: CANDIDATE, NOT YET COMPILED.

Unlike FrameOrderAudit, this file imports the actual production declarations.
It changes no production type and removes no fallback.  It verifies one exact
producer/consumer seam: the same-column `nv = k` branch of
`accum_block_on_closeThenBlock` (source 28349–28360) already obtains a native
`ResumeFrames P (FrameLevel.map k :: ks)` and destructures it twice.  Retaining
that frame subsumes both outputs, including the actual sibling reader at
30544–30550.  `P` is never replaced with the finished stream.

This does NOT prove all producers can supply this stronger face.  In
particular it does not remove `PackAlt`, `pendingFlow`, `scannerDrop`, the
optional cover, or the outer `Or True` of `pendingBlock.h_closeF`.
-/

set_option autoImplicit false

namespace NativeContinuationAudit

open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.IndentStackCover (FrameLevel)

variable {P : SurfPos → Prop} {n : Nat} {ks : List FrameLevel}

/-- Native equivalence: retain the mapping's own frame instead of separately
carrying its arbitrary-tail continuation.  Its bottom is exactly `P`. -/
lemma map_front_iff {sp : SurfPos} (h_lt : ∀ f ∈ ks, f.width < n) :
    ResumeFrames P (FrameLevel.map n :: ks) sp ↔
      (∀ sp_end, SCompactMapTail n sp sp_end → ResumeFrames P ks sp_end) := by
  constructor
  · intro h
    exact h.level_inv
  · intro h
    exact ResumeFrames.level n ks sp h_lt h

/-- The sequence-only face is a consequence, not a second obligation, whenever
the stronger native mapping frame has actually been supplied. -/
lemma native_pair_from_retained_map {sp : SurfPos}
    (h : ResumeFrames P (FrameLevel.map n :: ks) sp) :
    ResumeFrames P ks sp ∧
      (∀ sp_end, SCompactMapTail n sp sp_end → ResumeFrames P ks sp_end) :=
  ⟨h.level_inv sp (SCompactMapTail.nil n sp), h.level_inv⟩

/-- Exact paid birth of item 389, after the branch has established `nv = k`.
The input is the ORIGINAL `h_valF` mapping value continuation; the output
retains the same mapping frame instead of immediately eliminating it twice. -/
lemma landed_same_column_supply
    {sp_block sp_mid sp_dash sp_scan : SurfPos}
    (h_ssl : SSLComments sp_block sp_mid)
    (h_ind : SIndent n sp_mid sp_dash)
    (h_dash : GLit '-' sp_dash sp_scan)
    (h_gnot : GNot SNsChar sp_scan)
    (closeF : ∀ sp_end, SBlockNode (n + 1) .blockOut sp_block sp_end →
      ResumeFrames P (FrameLevel.map n :: ks) sp_end) :
    ∀ sp_final, SBlockIndented n .blockIn sp_scan sp_final →
      ∀ sp_end, SCompactSeqTail n sp_final sp_end →
        ResumeFrames P (FrameLevel.map n :: ks) sp_end := by
  intro sp_final h_indented sp_end h_tail
  exact closeF sp_end
    (valueLandedSeq (Nat.le_refl n) h_ssl
      (SBlockSeqEntries_of_compactTail h_ind h_dash h_gnot h_indented h_tail))

/-- Reconstruct the EXACT existing `pendingBlock.h_closeF` type from the
retained frame.  No constructor arity, caller, cover or scope changes.  The
same-column map-tail face is paid (left arm), not replaced by `True`. -/
lemma pendingBlock_closeF_from_retained_map
    {sc : ScannerState} {sp_start sp_scan : SurfPos}
    (h_lt : ∀ f ∈ ks, f.width < n)
    (h_cov : (∃ lo : Nat,
      L4YAML.Proofs.IndentStackCover.Floor lo n ks ∧
      L4YAML.Proofs.IndentStackCover.Covered lo ks sc) ∨ True)
    (h_strong : ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
      ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
        ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_end) :
    (∃ ks : List FrameLevel, (∀ f ∈ ks, f.width < n) ∧
      ((∃ lo : Nat, L4YAML.Proofs.IndentStackCover.Floor lo n ks ∧
        L4YAML.Proofs.IndentStackCover.Covered lo ks sc) ∨ True) ∧
      (∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
        ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
          ResumeFrames (SLYamlStream sp_start) ks sp_end) ∧
      (((∃ e, sc.indents.back? = some e ∧ e.isSequence = false) →
        ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
          ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
            ∀ sp_fin, SCompactMapTail n sp_end sp_fin →
              ResumeFrames (SLYamlStream sp_start) ks sp_fin) ∨ True)) ∨ True := by
  refine Or.inl ⟨ks, h_lt, h_cov, ?_, Or.inl ?_⟩
  · intro sp_mid h_node sp_end h_seq
    exact (native_pair_from_retained_map (h_strong sp_mid h_node sp_end h_seq)).1
  · intro _ sp_mid h_node sp_end h_seq sp_fin h_map
    exact (native_pair_from_retained_map (h_strong sp_mid h_node sp_end h_seq)).2
      sp_fin h_map

/-- The actual item-389 same-column sibling read: the awaited entry is empty,
the sequence tail is empty, and the mapping's tail remains.  This is the
native 30548–30550 consumer, with its exact returned frame list. -/
lemma same_column_sibling_reader
    {sp_scan sp_mid : SurfPos}
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_strong : ∀ sp_final, SBlockIndented n .blockIn sp_scan sp_final →
      ∀ sp_end, SCompactSeqTail n sp_final sp_end →
        ResumeFrames P (FrameLevel.map n :: ks) sp_end) :
    ∀ sp_fin, SCompactMapTail n sp_mid sp_fin → ResumeFrames P ks sp_fin :=
  (h_strong sp_mid (SBlockIndented.empty n .blockIn sp_scan sp_mid h_ssl)
    sp_mid (SCompactSeqTail.nil n sp_mid)).level_inv

/-- Guard the other actual native carrier: an explicit key's `ExplValueLine`
bottom is not collapsed to `SLYamlStream`.  No new same-column frame is
inserted under that bottom; this only reads a map frame already supplied. -/
lemma explicit_key_bottom_preserved
    {sp_start sp : SurfPos} {nv : Nat}
    (h : KeyFrames (ExplValueLine sp_start nv) (FrameLevel.map n :: ks) sp) :
    KeyFrames (ExplValueLine sp_start nv) ks sp ∧
      (∀ sp_end, SCompactMapTail n sp sp_end →
        KeyFrames (ExplValueLine sp_start nv) ks sp_end) := by
  cases h with
  | level _ _ _ _ h_cont =>
    exact ⟨h_cont sp (SCompactMapTail.nil n sp), h_cont⟩

/-- The old inner cover is not merely unpaid at a valid same-column mapping
top: it is impossible.  The floor cannot be raised above `n` to hide that map,
and every frame in the permitted list is strictly narrower than `n`. -/
lemma old_cover_impossible_at_own_mapping
    {sc : ScannerState}
    (h_top : sc.indents.back? = some
      ({ column := (n : Int), isSequence := false } : IndentEntry))
    (h_lt : ∀ f ∈ ks, f.width < n) :
    ¬ (∃ lo : Nat, L4YAML.Proofs.IndentStackCover.Floor lo n ks ∧
      L4YAML.Proofs.IndentStackCover.Covered lo ks sc) := by
  rintro ⟨lo, h_floor, h_cover⟩
  have h_mem := Array.mem_of_back? h_top
  have h_lo : (lo : Int) ≤ (n : Int) := by
    have h_bound := h_floor.1
    omega
  have h_frame : FrameLevel.map n ∈ ks := by
    simpa using h_cover _ h_mem rfl h_lo
  exact Nat.lt_irrefl n (h_lt (FrameLevel.map n) h_frame)

/-- Positive native transport on the exact existing scanner path: retain
`map n :: ks` both as continuation and as cover list.  Preprocessing may pop,
the directive-flag update leaves indents unchanged, and `-` preserves the
mapping cover.  The input floor is retained; no higher/vacuous floor is chosen.
This is the original producer's `h_cov_step`, specialized to its retained map. -/
lemma retained_map_cover_through_native_birth
    {lo : Nat} {sc s_prep s_birth s' : ScannerState}
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, '-')))
    (h_indents : s_birth.indents = s_prep.indents)
    (h_noflow : s_birth.inFlow = false)
    (h_birth : scanBlockEntry s_birth = .ok s')
    (h_floor : L4YAML.Proofs.IndentStackCover.Floor lo n
      (FrameLevel.map n :: ks))
    (h_cover : L4YAML.Proofs.IndentStackCover.Covered lo
      (FrameLevel.map n :: ks) sc) :
    L4YAML.Proofs.IndentStackCover.Floor lo n (FrameLevel.map n :: ks) ∧
      L4YAML.Proofs.IndentStackCover.Covered lo (FrameLevel.map n :: ks) s' :=
  ⟨h_floor, L4YAML.Proofs.IndentStackCover.scanBlockEntry_cover h_noflow h_birth
    ((L4YAML.Proofs.IndentStackCover.preprocess_cover h_pre h_cover).of_indents_eq
      h_indents)⟩

#print axioms map_front_iff
#print axioms native_pair_from_retained_map
#print axioms landed_same_column_supply
#print axioms pendingBlock_closeF_from_retained_map
#print axioms same_column_sibling_reader
#print axioms explicit_key_bottom_preserved
#print axioms old_cover_impossible_at_own_mapping
#print axioms retained_map_cover_through_native_birth

end NativeContinuationAudit
