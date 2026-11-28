import L4YAML.Proofs.Production.StreamAccum

set_option autoImplicit false
open L4YAML L4YAML.Surface

namespace R2ContinuationPrimitives

-- This is the parent's proved, tail-parametric grammar primitive, made an
-- explicit research dependency. It is absent from the qualified #392 source.
-- Keeping P arbitrary preserves every later ancestor obligation.
lemma compactEntryRoute {P : SurfPos → Prop} {n m : Nat} {ctx : YamlContext}
    {sp_entry sp_ind : SurfPos}
    (route : ∀ sp_e, SBlockIndented n ctx sp_entry sp_e → P sp_e)
    (indent : SIndent m sp_entry sp_ind) :
    ∀ sp_v, SBlockMapEntry (n + 1 + m) sp_ind sp_v →
      ∀ sp_e, SCompactMapTail (n + 1 + m) sp_v sp_e → P sp_e :=
  fun sp_v entry sp_e tail => route sp_e
    (SBlockIndented.compactMap n ctx m sp_entry sp_ind sp_e indent
      (SCompactMap.mk (n + 1 + m) sp_ind sp_v sp_e entry tail))

#print axioms compactEntryRoute

end R2ContinuationPrimitives
