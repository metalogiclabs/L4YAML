import L4YAML.Proofs.Production.StreamAccum
set_option autoImplicit false
open L4YAML L4YAML.Surface
namespace L4YAML.Proofs.StreamAccum
/-- Complete this actual explicit entry's key without closing away its value.
    The result predicate is arbitrary: it may itself await an enclosing value.
    Used by `explEntryChain_of_keyContent` and the compact entry producers on
    the path to `scan_content_gives_stream_v2`. -/
lemma explicitEntryValueRoute {P : SurfPos → Prop} {n : Nat}
    {sp_q sp_key : SurfPos} (h_q : GLit '?' sp_q sp_key)
    (route : ∀ sp_e, SBlockMapEntry n sp_q sp_e → P sp_e) :
    ∀ sp_m, SBlockIndented n .blockOut sp_key sp_m →
      ∀ sp_i sp_c, SIndent n sp_m sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v, SBlockIndented n .blockOut sp_c sp_v → P sp_v :=
  fun sp_m h_key sp_i sp_c h_ind h_lit sp_v h_value =>
    route sp_v (SBlockMapEntry.explicit n sp_q sp_key sp_m sp_i sp_c sp_v
      h_q h_key h_ind h_lit h_value)

/-- Plug a whole compact mapping entry into its actual enclosing slot.
    Keep the caller's result predicate, including an unfinished explicit value,
    rather than choosing the enclosing entry's `explicitEmpty` alternative.
    The compact producers and `compactExplicitKeyFrame` consume this route. -/
lemma compactEntryRoute {P : SurfPos → Prop} {n m : Nat} {ctx : YamlContext}
    {sp_entry sp_ind : SurfPos}
    (route : ∀ sp_e, SBlockIndented n ctx sp_entry sp_e → P sp_e)
    (h_ind : SIndent m sp_entry sp_ind) :
    ∀ sp_e, SBlockMapEntry (n + 1 + m) sp_ind sp_e → P sp_e :=
  fun sp_e h_entry => route sp_e
    (SBlockIndented.compactMap n ctx m sp_entry sp_ind sp_e h_ind
      (SCompactMap.mk (n + 1 + m) sp_ind sp_e sp_e h_entry
        (SCompactMapTail.nil (n + 1 + m) sp_e)))


end L4YAML.Proofs.StreamAccum

set_option autoImplicit false
open L4YAML L4YAML.Surface L4YAML.Proofs.StreamAccum

-- A value line stays an obligation, so the result can itself await another value.
def AwaitValue (P : SurfPos → Prop) (n : Nat) (e : SurfPos) : Prop :=
  ∀ i c, SIndent n e i → GLit ':' i c →
    ∀ v, SBlockIndented n .blockOut c v → P v

-- The three questions in the real P144 witness have these compact-key indices.
-- This checks the complete constructor ordering for three future values; an
-- early explicitEmpty projection cannot inhabit the required result.
example {P : SurfPos → Prop} {n m₀ m₁ : Nat}
    {q₀ k₀ q₁ k₁ q₂ k₂ : SurfPos}
    (root : ∀ e, SBlockMapEntry n q₀ e → P e)
    (question₀ : GLit '?' q₀ k₀) (indent₀ : SIndent m₀ k₀ q₁)
    (question₁ : GLit '?' q₁ k₁) (indent₁ : SIndent m₁ k₁ q₂)
    (question₂ : GLit '?' q₂ k₂) :
    ∀ e, SBlockIndented (n + 1 + m₀ + 1 + m₁) .blockOut k₂ e →
      AwaitValue (AwaitValue (AwaitValue P n) (n + 1 + m₀))
        (n + 1 + m₀ + 1 + m₁) e := by
  have parent := explicitEntryValueRoute question₀ root
  have child := compactEntryRoute parent indent₀
  have middle := explicitEntryValueRoute question₁ child
  have grandchild := compactEntryRoute middle indent₁
  exact explicitEntryValueRoute question₂ grandchild

-- The source question and grammar index cannot be silently substituted.
example {P : SurfPos → Prop} {n : Nat} {q q' key : SurfPos}
    (route : ∀ e, SBlockMapEntry n q e → P e)
    (question : GLit '?' q key) (other : GLit '?' q' key) :
    ∀ e, SBlockIndented n .blockOut key e → AwaitValue P n e := by
  fail_if_success exact explicitEntryValueRoute other route
  fail_if_success exact (explicitEntryValueRoute (n := n + 1) question route)
  exact explicitEntryValueRoute question route

#print axioms compactEntryRoute
#print axioms explicitEntryValueRoute
