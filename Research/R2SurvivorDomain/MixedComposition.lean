import L4YAML.Proofs.Production.StreamAccum

set_option autoImplicit false
open L4YAML L4YAML.Surface L4YAML.Proofs.StreamAccum

namespace R2SurvivorDomain

def AwaitValue (P : SurfPos → Prop) (n : Nat) (e : SurfPos) : Prop :=
  ∀ i c, SIndent n e i → GLit ':' i c →
    ∀ v, SBlockIndented n .blockOut c v → P v

-- Conditional grammar composition for the initialized native 6/2/0 control:
-- q3 owns a real value, q2 has an omitted value, q1 and q0 still await theirs.
-- The omitted entry closes only AFTER its key (including q3's value) completes.
-- This checks the entry route contract used by the actual compact producers;
-- it does not manufacture that route for an arbitrary reachable scanner state.
example {P : SurfPos → Prop} {n m₀ m₁ m₂ : Nat}
    {q₀ k₀ q₁ k₁ q₂ k₂ q₃ k₃ keyEnd i c valueEnd : SurfPos}
    (root : ∀ e, SBlockMapEntry n q₀ e → P e)
    (question₀ : GLit '?' q₀ k₀) (indent₀ : SIndent m₀ k₀ q₁)
    (question₁ : GLit '?' q₁ k₁) (indent₁ : SIndent m₁ k₁ q₂)
    (question₂ : GLit '?' q₂ k₂) (indent₂ : SIndent m₂ k₂ q₃)
    (question₃ : GLit '?' q₃ k₃)
    (key : SBlockIndented (n + 1 + m₀ + 1 + m₁ + 1 + m₂) .blockOut k₃ keyEnd)
    (valueIndent : SIndent (n + 1 + m₀ + 1 + m₁ + 1 + m₂) keyEnd i)
    (colon : GLit ':' i c)
    (value : SBlockIndented (n + 1 + m₀ + 1 + m₁ + 1 + m₂) .blockOut c valueEnd) :
    AwaitValue (AwaitValue P n) (n + 1 + m₀) valueEnd := by
  have rootKey := explicitEntryValueRoute question₀ root
  have entry₁ := fun e h => compactEntryRoute rootKey indent₀ e h e
    (SCompactMapTail.nil (n + 1 + m₀) e)
  have key₁ := explicitEntryValueRoute question₁ entry₁
  have entry₂ := fun e h => compactEntryRoute key₁ indent₁ e h e
    (SCompactMapTail.nil (n + 1 + m₀ + 1 + m₁) e)
  have key₂ := fun e h => entry₂ e
    (SBlockMapEntry.explicitEmpty (n + 1 + m₀ + 1 + m₁) q₂ k₂ e question₂ h)
  have entry₃ := fun e h => compactEntryRoute key₂ indent₂ e h e
    (SCompactMapTail.nil (n + 1 + m₀ + 1 + m₁ + 1 + m₂) e)
  exact explicitEntryValueRoute question₃ entry₃ keyEnd key i c valueIndent colon valueEnd value

-- Retain every value instead: identical real questions, different completion.
example {P : SurfPos → Prop} {n m₀ m₁ m₂ : Nat}
    {q₀ k₀ q₁ k₁ q₂ k₂ q₃ k₃ : SurfPos}
    (root : ∀ e, SBlockMapEntry n q₀ e → P e)
    (question₀ : GLit '?' q₀ k₀) (indent₀ : SIndent m₀ k₀ q₁)
    (question₁ : GLit '?' q₁ k₁) (indent₁ : SIndent m₁ k₁ q₂)
    (question₂ : GLit '?' q₂ k₂) (indent₂ : SIndent m₂ k₂ q₃)
    (question₃ : GLit '?' q₃ k₃) :
    ∀ e, SBlockIndented (n + 1 + m₀ + 1 + m₁ + 1 + m₂) .blockOut k₃ e →
      AwaitValue (AwaitValue (AwaitValue (AwaitValue P n) (n + 1 + m₀))
        (n + 1 + m₀ + 1 + m₁)) (n + 1 + m₀ + 1 + m₁ + 1 + m₂) e := by
  have rootKey := explicitEntryValueRoute question₀ root
  have entry₁ := fun e h => compactEntryRoute rootKey indent₀ e h e
    (SCompactMapTail.nil (n + 1 + m₀) e)
  have key₁ := explicitEntryValueRoute question₁ entry₁
  have entry₂ := fun e h => compactEntryRoute key₁ indent₁ e h e
    (SCompactMapTail.nil (n + 1 + m₀ + 1 + m₁) e)
  have key₂ := explicitEntryValueRoute question₂ entry₂
  have entry₃ := fun e h => compactEntryRoute key₂ indent₂ e h e
    (SCompactMapTail.nil (n + 1 + m₀ + 1 + m₁ + 1 + m₂) e)
  exact explicitEntryValueRoute question₃ entry₃

-- Exact source identity and grammar index remain mandatory.
example {P : SurfPos → Prop} {n : Nat} {q q' key : SurfPos}
    (route : ∀ e, SBlockMapEntry n q e → P e)
    (question : GLit '?' q key) (other : GLit '?' q' key) :
    ∀ e, SBlockIndented n .blockOut key e → AwaitValue P n e := by
  fail_if_success exact explicitEntryValueRoute other route
  fail_if_success exact explicitEntryValueRoute (n := n + 1) question route
  exact explicitEntryValueRoute question route

#print axioms explicitEntryValueRoute
#print axioms compactEntryRoute

end R2SurvivorDomain
