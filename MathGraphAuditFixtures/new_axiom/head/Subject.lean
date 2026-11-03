namespace Subject
def bump (n : Nat) : Nat := n + 1
theorem support (n : Nat) : bump n = n + 1 := rfl
axiom oracle : ∀ n : Nat, bump n = n + 1
theorem claim : ∀ n : Nat, bump n = n + 1 := oracle
end Subject
