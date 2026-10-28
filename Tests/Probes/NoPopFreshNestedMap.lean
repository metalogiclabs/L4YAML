import L4YAML.Proofs.Production.StreamAccum

/-!
The no-pop scanner category also includes a fresh mapping nested in a
pending block-sequence entry.  Such a mapping is an awaited VALUE node,
not a sibling of a mapping level already on the resume frame stack.

This tests the actual `PendingNode.pendingBlock.h_close` interface and the
surface production constructors, without claiming execution reaches a
particular proof branch.
-/

open L4YAML.Surface

namespace L4YAML.Proofs.StreamAccum

/-- A mapping freshly opened at `k` inside a pending sequence entry at `n`
    fills that entry's awaited block node.  No old mapping-frame membership
    or sequence-tail-to-map-tail coercion is required. -/
lemma pending_sequence_fresh_map {P : SurfPos → Prop} {n k : Nat}
    {s s₂ s_ind : SurfPos}
    (h_le : n + 1 ≤ k)
    (h_ssl : SSLComments s s₂)
    (h_indent : SIndent k s₂ s_ind)
    (closeEntry : ∀ b, SBlockIndented n .blockIn s b → P b) :
    ∀ b, SBlockMapEntry k s_ind b →
      ∀ c, SCompactMapTail k b c → P c := by
  intro b h_entry c h_tail
  apply closeEntry c
  apply SBlockIndented.node n .blockIn s c
  exact nestedBlockMap h_le h_ssl
    (L4YAML.Proofs.NodeProduction.SBlockMapEntries_of_compactTail
      h_indent h_entry h_tail)

/-- Pair of routes consumed by an opener: close its first entry or retain
    its whole compact tail for later sibling entries.  The first entry is
    mandatory in the premise, unlike `h_res_land` at `s₂`, whose nil tail
    would incorrectly require a completed mapping before any entry exists. -/
lemma pending_sequence_fresh_map_routes {P : SurfPos → Prop} {n k : Nat}
    {s s₂ s_ind : SurfPos}
    (h_le : n + 1 ≤ k)
    (h_ssl : SSLComments s s₂)
    (h_indent : SIndent k s₂ s_ind)
    (closeEntry : ∀ b, SBlockIndented n .blockIn s b → P b) :
    (∀ b, SBlockMapEntry k s_ind b → P b) ∧
    (∀ b, SBlockMapEntry k s_ind b →
      ∀ c, SCompactMapTail k b c → ResumeFrames P [] c) := by
  let route := pending_sequence_fresh_map h_le h_ssl h_indent closeEntry
  constructor
  · intro b h_entry
    exact route b h_entry b (SCompactMapTail.nil k b)
  · intro b h_entry c h_tail
    exact ResumeFrames.bottom c (route b h_entry c h_tail)

example {P : SurfPos → Prop} {n k : Nat} {s s₂ s_ind : SurfPos}
    (h_le : n + 1 ≤ k)
    (h_ssl : SSLComments s s₂)
    (h_indent : SIndent k s₂ s_ind)
    (closeEntry : ∀ b, SBlockIndented n .blockIn s b → P b) :
    ∀ b, SBlockMapEntry k s_ind b →
      ∀ c, SCompactMapTail k b c → P c :=
  pending_sequence_fresh_map h_le h_ssl h_indent closeEntry

-- The two route faces that `colon_open_map` and `question_open_map` build:
-- a closed entry and a tail-open entry.  This is stronger and better typed
-- for a fresh nested mapping than `h_res_land` at the unfilled landing.
example {P : SurfPos → Prop} {n k : Nat} {s s₂ s_ind : SurfPos}
    (h_le : n + 1 ≤ k)
    (h_ssl : SSLComments s s₂)
    (h_indent : SIndent k s₂ s_ind)
    (closeEntry : ∀ b, SBlockIndented n .blockIn s b → P b) :
    (∀ b, SBlockMapEntry k s_ind b → P b) ∧
    (∀ b, SBlockMapEntry k s_ind b →
      ∀ c, SCompactMapTail k b c → ResumeFrames P [] c) :=
  pending_sequence_fresh_map_routes h_le h_ssl h_indent closeEntry

#print axioms pending_sequence_fresh_map
#print axioms pending_sequence_fresh_map_routes

end L4YAML.Proofs.StreamAccum
