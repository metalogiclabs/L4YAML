namespace Subject
def bump (n : Nat) : Nat := n + 1
theorem support (n : Nat) : bump n = n + 1 := rfl
theorem claim : ∀ n : Nat, bump n = n + 1 := support
end Subject
