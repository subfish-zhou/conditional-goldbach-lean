module

import Mathlib.Tactic.NormNum.Prime
public import ConditionalGoldbach.Proofs.Elementary

/-! A rational lower bound for the universal odd-prime Euler product. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
open MathlibNt.SieveTheory.SingularSeries hiding singularSeries

lemma liuUniversalProductTruncated_lower (n : ℕ) :
    9 * (n + 4 : ℝ) / (16 * (n + 3 : ℝ)) ≤ liuUniversalProductTruncated (n+4) := by
  induction n with
  | zero => norm_num [liuUniversalProductTruncated, liuBaseDeviation, Finset.prod_range_succ]
  | succ n ih =>
    have hx : (4 : ℝ) ≤ n+4 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hx0 : (n : ℝ)+4 ≠ 0 := by positivity
    have hy0 : (n : ℝ)+3 ≠ 0 := by positivity
    have hg : 0 ≤ 1 - 1 / ((n : ℝ)+4)^2 := by
      have he : 1 ≤ ((n : ℝ)+4)^2 := by nlinarith
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) he
      simpa only [one_div_one, sub_nonneg] using this
    have hfac : 1 - 1 / ((n : ℝ)+4)^2 ≤ 1 + liuBaseDeviation (n+5) := by
      unfold liuBaseDeviation
      split_ifs
      · push_cast
        ring_nf
        rfl
      · simp
        positivity
    have hstep : liuUniversalProductTruncated (n+1+4) =
        liuUniversalProductTruncated (n+4) * (1+liuBaseDeviation (n+5)) := by
      unfold liuUniversalProductTruncated
      rw [show n+1+4+1 = (n+4+1)+1 by omega, Finset.prod_range_succ]
    rw [hstep]
    have heq : 9 * ((n+1 : ℕ)+4 : ℝ) / (16 * ((n+1 : ℕ)+3 : ℝ)) =
        (9 * (n+4 : ℝ)/(16*(n+3 : ℝ))) * (1-1/((n : ℝ)+4)^2) := by
      push_cast
      field_simp
      ring
    rw [heq]
    exact mul_le_mul ih hfac hg (liuUniversalProductTruncated_pos (n+4)).le

lemma C2_lower : (9 : ℝ)/16 ≤ C2 := by
  change (9 : ℝ)/16 ≤ liuUniversalProduct
  apply ge_of_tendsto tendsto_liuUniversalProductTruncated
  filter_upwards [eventually_ge_atTop 4] with z hz
  obtain ⟨n, rfl⟩ : ∃ n, z = n+4 := ⟨z-4, by omega⟩
  apply le_trans _ (liuUniversalProductTruncated_lower n)
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ)<16) (by positivity : 0 < 16*(n+3 : ℝ))]
  nlinarith

lemma singularSeries_gt_one (N : ℕ) : 1 < singularSeries N := by
  have h := singularSeries_uniform_lower N
  linarith [C2_lower]

end ConditionalGoldbach
