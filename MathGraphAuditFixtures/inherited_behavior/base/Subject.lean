namespace Subject
def bump (n : Nat) : Nat := n + 2
theorem support (n : Nat) : bump n = n + 2 := rfl
theorem claim : ∀ n : Nat, bump n = n + 2 := support
end Subject
