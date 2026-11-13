namespace ComparatorControl
theorem check : ∀ n : Nat, ∃ m : Nat, m = m := by intro n; exact ⟨0, rfl⟩
end ComparatorControl
