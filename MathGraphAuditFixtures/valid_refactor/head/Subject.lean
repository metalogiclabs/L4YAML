namespace Subject
def bump (n : Nat) : Nat := Nat.succ n
theorem support (n : Nat) : bump n = Nat.succ n := rfl
theorem claim : ∀ n : Nat, bump n = Nat.succ n := support
end Subject
