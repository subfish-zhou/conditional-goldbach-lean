namespace ComparatorControl
theorem check : ∃ m : Nat, ∀ n : Nat, m = m := by exact ⟨0, fun _ => rfl⟩
end ComparatorControl
