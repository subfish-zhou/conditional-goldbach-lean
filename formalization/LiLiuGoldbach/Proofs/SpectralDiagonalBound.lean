import LiLiuGoldbach.Proofs.SpectralDiagonalOperator
import LiLiuGoldbach.Proofs.SpectralTraceBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace Asymptotics
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

theorem mangoldt_partialSum_eq_psi (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, mangoldt k) = Chebyshev.psi n := by
  have he : Finset.Icc 1 n = Finset.Ioc 0 n := by ext k; simp; omega
  simp only [Chebyshev.psi, Nat.floor_natCast, mangoldt, he]

theorem mangoldt_partialSum_bigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, mangoldt k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  apply IsBigO.of_bound (Real.log 4 + 4)
  apply Eventually.of_forall
  intro n
  rw [mangoldt_partialSum_eq_psi, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg _),
    Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

/-- Chebyshev's estimate bounds the positive von Mangoldt Dirichlet series uniformly near its pole. -/
theorem mangoldt_LSeries_bound (x : ℝ) (hx : 0 < x) :
    ‖LSeries (fun n => (mangoldt n : ℂ)) (1 + x)‖ ≤
      (1 + x) * (Real.log 4 + 4) / x := by
  have hnonneg (n : ℕ) : 0 ≤ mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  rw [LSeries_eq_mul_integral_of_nonneg mangoldt (r := 1) zero_le_one
    (by simp only [add_re, one_re, ofReal_re]; linarith) mangoldt_partialSum_bigO hnonneg, norm_mul]
  have hs : ‖(1 : ℂ) + x‖ = 1 + x := by
    rw [← ofReal_one, ← ofReal_add, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hs]
  have hi := (integrableOn_Ioi_rpow_of_lt (show -1 - x < -1 by linarith) zero_lt_one).const_mul
    (Real.log 4 + 4)
  have hbound : ‖∫ t : ℝ in Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (mangoldt k : ℂ)) * (t : ℂ) ^ (-((1 : ℂ) + x + 1))‖ ≤
      (Real.log 4 + 4) / x := by
    have hn := norm_integral_le_of_norm_le hi (f := fun t : ℝ =>
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (mangoldt k : ℂ)) * (t : ℂ) ^ (-((1 : ℂ) + x + 1))) ?_
    · convert hn using 1
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -1 - x < -1) zero_lt_one]
      simp only [Real.one_rpow]
      ring_nf
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      have hsum : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (mangoldt k : ℂ)) = (Chebyshev.psi t : ℂ) := by
        have he : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ := by ext k; simp; omega
        simp only [Chebyshev.psi, mangoldt, he, ofReal_sum]
      rw [norm_mul, hsum, norm_real, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg _),
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re, ofReal_re]
      calc
        _ ≤ ((Real.log 4 + 4) * t) * t ^ (-(1 + x + 1)) :=
          mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self ht0.le) (Real.rpow_nonneg ht0.le _)
        _ = (Real.log 4 + 4) * t ^ (-1 - x) := by
          rw [mul_assoc]
          congr 1
          nth_rw 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht0]
          congr 1
          ring
  calc
    _ ≤ (1 + x) * ((Real.log 4 + 4) / x) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- The positive real von Mangoldt series is summable and satisfies the Chebyshev bound. -/
theorem mangoldt_positive_series_bound (x : ℝ) (hx : 0 < x) :
    Summable (fun j : ℕ => mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x)) ∧
      (∑' j : ℕ, mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x)) ≤
        (1 + x) * (Real.log 4 + 4) / x := by
  have hS : LSeriesSummable (fun n => (mangoldt n : ℂ)) (1 + x) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp only [add_re, one_re, ofReal_re]; linarith)
  have ht (j : ℕ) : LSeries.term (fun n => (mangoldt n : ℂ)) (1 + x) (j + 1) =
      ((mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x) : ℝ) : ℂ) := by
    rw [LSeries.term_of_ne_zero (by omega), ofReal_div, Complex.ofReal_cpow (by positivity)]
    simp only [ofReal_natCast, ofReal_add, ofReal_one]
  have hnorm (j : ℕ) : ‖LSeries.term (fun n => (mangoldt n : ℂ)) (1 + x) (j + 1)‖ =
      mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x) := by
    rw [ht, norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
  have hsum : Summable (fun j : ℕ => mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x)) := by
    simpa only [hnorm] using (summable_nat_add_iff 1).mpr hS.norm
  refine ⟨hsum, ?_⟩
  have heq : ‖LSeries (fun n => (mangoldt n : ℂ)) (1 + x)‖ =
      ∑' j : ℕ, mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x) := by
    rw [LSeries, hS.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    simp only [ht, ← Complex.ofReal_tsum, norm_real, Real.norm_eq_abs]
    apply abs_of_nonneg
    exact tsum_nonneg (fun j => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (by positivity) _))
  rw [← heq]
  exact mangoldt_LSeries_bound x hx

/-- The squared von Mangoldt coefficients have a uniform inverse-square bound. -/
theorem diagonalCoefficient_series_bound (N : ℕ) (x : ℝ) (hx : 0 < x) :
    (∑' j, diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * x)) ≤
      (1 + x) * (Real.log 4 + 4) / x ^ 2 := by
  have hm := mangoldt_positive_series_bound x hx
  have hterm (j : ℕ) : diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * x) ≤
      x⁻¹ * (mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x)) := by
    let n : ℝ := (j + 1 : ℕ)
    have hn : 0 < n := by dsimp [n]; positivity
    have hΛ : 0 ≤ mangoldt (j + 1) := ArithmeticFunction.vonMangoldt_nonneg
    have hlog : mangoldt (j + 1) ≤ n ^ x / x :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_rpow_div hn.le hx)
    have hc : diagonalCoefficient N j ≤ mangoldt (j + 1) ^ 2 / n := by
      unfold diagonalCoefficient
      split_ifs
      · rfl
      · exact div_nonneg (sq_nonneg _) hn.le
    change diagonalCoefficient N j * n ^ (-2 * x) ≤ x⁻¹ * (mangoldt (j + 1) / n ^ (1 + x))
    calc
      _ ≤ (mangoldt (j + 1) ^ 2 / n) * n ^ (-2 * x) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn.le _)
      _ = mangoldt (j + 1) * (mangoldt (j + 1) / n * n ^ (-2 * x)) := by ring
      _ ≤ (n ^ x / x) * (mangoldt (j + 1) / n * n ^ (-2 * x)) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
      _ = _ := by
        rw [show -2 * x = -(x + x) by ring, Real.rpow_neg hn.le,
          Real.rpow_add hn, Real.rpow_add hn, Real.rpow_one]
        field_simp [hx.ne', hn.ne', (Real.rpow_pos_of_pos hn x).ne']
  calc
    _ ≤ ∑' j, x⁻¹ * (mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x)) :=
      Summable.tsum_le_tsum hterm (diagonalCoefficient_power_summable N x hx) (hm.1.mul_left x⁻¹)
    _ = x⁻¹ * (∑' j, mangoldt (j + 1) / (j + 1 : ℕ) ^ (1 + x)) := tsum_mul_left
    _ ≤ x⁻¹ * ((1 + x) * (Real.log 4 + 4) / x) :=
      mul_le_mul_of_nonneg_left hm.2 (inv_nonneg.mpr hx.le)
    _ = _ := by ring

/-- The original diagonal operator has the paper's uniform inverse-square trace bound. -/
theorem diagonalOperator_trace_bound {a : ℝ} (ha : a < beta) (ha0 : 0 < a)
    (N : ℕ) [NeZero N] :
    IsPositiveTraceClass (diagonalOperator ha N) ∧
      hsNorm (diagonalOperator ha N) ≤ positiveTrace (diagonalOperator ha N) ∧
      positiveTrace (diagonalOperator ha N) ≤
        (2 * Real.pi * (Real.log 4 + 4)) * a⁻¹ ^ 2 := by
  have hs := diagonalOperator_positiveTraceClass ha ha0 N
  have hb : 0 < beta := by norm_num [beta]
  have hC : 0 < Real.log 4 + 4 := by positivity
  refine ⟨hs.1, hs.1.hsNorm_le_trace, ?_⟩
  rw [hs.2]
  have h₁ := mul_le_mul_of_nonneg_left (diagonalCoefficient_series_bound N a ha0)
    (div_nonneg Real.pi_pos.le (by positivity : 0 ≤ 1 + a))
  have h₂ := mul_le_mul_of_nonneg_left (diagonalCoefficient_series_bound N beta hb)
    (div_nonneg Real.pi_pos.le (by positivity : 0 ≤ 1 + beta))
  have he₁ : Real.pi / (1 + a) * ((1 + a) * (Real.log 4 + 4) / a ^ 2) =
      Real.pi * (Real.log 4 + 4) * a⁻¹ ^ 2 := by field_simp
  have he₂ : Real.pi / (1 + beta) * ((1 + beta) * (Real.log 4 + 4) / beta ^ 2) =
      Real.pi * (Real.log 4 + 4) * beta⁻¹ ^ 2 := by norm_num [beta]; ring
  rw [he₁] at h₁
  rw [he₂] at h₂
  have hpow : beta⁻¹ ^ 2 ≤ a⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hb.le) (inv_le_inv₀ hb ha0 |>.mpr ha.le) 2
  have hbound := mul_le_mul_of_nonneg_left hpow (mul_nonneg Real.pi_pos.le hC.le)
  nlinarith

end LiLiuGoldbach16
