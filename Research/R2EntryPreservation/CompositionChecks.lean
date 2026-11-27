import L4YAML.Proofs.Production.StreamAccum

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
  have child := fun e h => compactEntryRoute parent indent₀ e h e
    (SCompactMapTail.nil (n + 1 + m₀) e)
  have middle := explicitEntryValueRoute question₁ child
  have grandchild := fun e h => compactEntryRoute middle indent₁ e h e
    (SCompactMapTail.nil (n + 1 + m₀ + 1 + m₁) e)
  exact explicitEntryValueRoute question₂ grandchild

-- The source question and grammar index cannot be silently substituted.
example {P : SurfPos → Prop} {n : Nat} {q q' key : SurfPos}
    (route : ∀ e, SBlockMapEntry n q e → P e)
    (question : GLit '?' q key) (_other : GLit '?' q' key) :
    ∀ e, SBlockIndented n .blockOut key e → AwaitValue P n e := by
  fail_if_success exact explicitEntryValueRoute _other route
  fail_if_success exact (explicitEntryValueRoute (n := n + 1) question route)
  exact explicitEntryValueRoute question route

-- Siblings of the completed inner entry stay inside the same enclosing key.
example {P : SurfPos → Prop} {n m : Nat} {ctx : YamlContext}
    {key q innerEnd keyEnd : SurfPos}
    (parent : ∀ e, SBlockIndented n ctx key e → P e)
    (indent : SIndent m key q)
    (entry : SBlockMapEntry (n + 1 + m) q innerEnd)
    (siblings : SCompactMapTail (n + 1 + m) innerEnd keyEnd) : P keyEnd :=
  compactEntryRoute parent indent innerEnd entry keyEnd siblings

#print axioms compactEntryRoute
#print axioms explicitEntryValueRoute
