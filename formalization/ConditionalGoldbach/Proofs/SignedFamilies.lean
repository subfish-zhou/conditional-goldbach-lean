module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity

/-! The three disjoint arithmetic families used by Mellin projection. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter Set Complex
namespace ConditionalGoldbach

lemma difference_congruence_families (N n m : ℕ) (hnm : n ≠ m) :
    ((n : ZMod N) = m) ↔
      (∃ k : ℕ, 0 < k ∧ m = n + k * N) ∨ (∃ k : ℕ, 0 < k ∧ n = m + k * N) := by
  rw [ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).mp h
      have hk0 : 0 < k := by
        by_contra hn
        have : k = 0 := by omega
        simp [this] at hk
        omega
      exact Or.inl ⟨k, hk0, by rw [mul_comm N k] at hk; omega⟩
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hgt.le).mp h.symm
      have hk0 : 0 < k := by
        by_contra hn
        have : k = 0 := by omega
        simp [this] at hk
        omega
      exact Or.inr ⟨k, hk0, by rw [mul_comm N k] at hk; omega⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · simp
    · simp

lemma sum_congruence_family (N n m : ℕ) (hn : 0 < n) (_hm : 0 < m) :
    ((n : ZMod N) = -(m : ZMod N)) ↔ ∃ k : ℕ, 0 < k ∧ n + m = k * N := by
  have hc : ((n : ZMod N) = -(m : ZMod N)) ↔ N ∣ n + m := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, add_eq_zero_iff_eq_neg]
  rw [hc]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, by simpa [mul_comm] using hk⟩
    by_contra hk0
    have : k = 0 := by omega
    simp [this] at hk
    omega
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, by simpa [mul_comm] using heq⟩

end ConditionalGoldbach
