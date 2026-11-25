module
public import Tests.Guards.Proofs.ExplicitWordFragment
@[expose] public section Blanket
namespace L4YAML.Tests.Guards.AnchoredWordSource
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Tests.Guards.ExplicitWordFragment

-- Blueprint 7.7: independent source family → initialized scan/fold and TraceOf.
def suffix (v : List Char) : List Char := '&' :: 'a' :: ' ' :: v
def source (k v : List Char) : String := ExplicitWordFragment.source k (suffix v)

lemma suffix_bytes (v : List Char) (hv : ∀ c ∈ v, Letter c) :
 L4YAML.Proofs.CouplingBridge.listByteSize (suffix v) = 3+v.length := by
 have hvb : L4YAML.Proofs.CouplingBridge.listByteSize v = v.length := by
  induction v with
  | nil => rfl
  | cons c cs ih =>
   simp only [L4YAML.Proofs.CouplingBridge.listByteSize,List.length_cons,
    (letter_facts (hv c (by simp))).2.2.2.2.2.2.2.1]
   rw [ih (fun d hd => hv d (by simp [hd]))]; omega
 simp [suffix,L4YAML.Proofs.CouplingBridge.listByteSize,hvb,
  show '&'.utf8Size=1 from by decide,show 'a'.utf8Size=1 from by decide,
  show ' '.utf8Size=1 from by decide]; omega
end L4YAML.Tests.Guards.AnchoredWordSource
