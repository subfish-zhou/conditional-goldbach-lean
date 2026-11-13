import ConditionalGoldbach.Proofs.SpectralDiagonalTrace
import ConditionalGoldbach.Proofs.SpectralHardyRankSeries
import ConditionalGoldbach.Proofs.HardyKernelOperator

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- The genuine holomorphic function corresponding to a diagonal rank-one vector. -/
def diagonalRankFunction (N j : ℕ) (s : ℂ) : ℂ :=
  (Real.sqrt (diagonalCoefficient N j) : ℂ) * diagonalVector (j + 1) s

theorem diagonalRankFunction_fourierLaplace {a : ℝ} (ha : a < beta) (ha0 : 0 ≤ a)
    (N j : ℕ) (s : ℂ) (hs : s ∈ strip a beta) :
    fourierLaplace (diagonalRankVector (a := a) N j) s = diagonalRankFunction N j s := by
  rw [diagonalRankVector, fourierLaplace_smul _ _ hs,
    (diagonalHardyVector_spec ha ha0 _ (by omega)).1 s hs]
  rfl

theorem diagonalRankFunction_boundary {a : ℝ} (ha : a < beta) (ha0 : 0 ≤ a) (N j : ℕ) :
    ((boundaryTraces ha (diagonalRankVector (a := a) N j)).1 =ᵐ[volume]
      fun t => diagonalRankFunction N j (line a t)) ∧
    ((boundaryTraces ha (diagonalRankVector (a := a) N j)).2 =ᵐ[volume]
      fun t => diagonalRankFunction N j (line beta t)) := by
  have hv := diagonalHardyVector_spec ha ha0 (j + 1) (by omega)
  simp only [diagonalRankVector, boundaryTraces_smul]
  constructor
  · filter_upwards [Lp.coeFn_smul (Real.sqrt (diagonalCoefficient N j) : ℂ)
      (boundaryTraces ha (diagonalHardyVector (j + 1))).1, hv.2.1] with t ht htd
    change (((Real.sqrt (diagonalCoefficient N j) : ℂ) •
      (boundaryTraces ha (diagonalHardyVector (j + 1))).1) t) = _
    rw [ht, Pi.smul_apply, smul_eq_mul, htd]
    rfl
  · filter_upwards [Lp.coeFn_smul (Real.sqrt (diagonalCoefficient N j) : ℂ)
      (boundaryTraces ha (diagonalHardyVector (j + 1))).2, hv.2.2] with t ht htd
    change (((Real.sqrt (diagonalCoefficient N j) : ℂ) •
      (boundaryTraces ha (diagonalHardyVector (j + 1))).2) t) = _
    rw [ht, Pi.smul_apply, smul_eq_mul, htd]
    rfl

/-- Conjugation of a diagonal vector introduces exactly the conjugate spectral variable. -/
theorem diagonalVector_conj (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    conj (diagonalVector n z) = (n : ℂ) ^ (-conj z) / (1 + conj z) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  simp only [diagonalVector, map_div₀, map_add, map_one]
  congr 1
  simpa only [map_neg, map_natCast] using (Complex.cpow_conj (n : ℂ) (-z) harg).symm

/-- A single diagonal term agrees with its Dirichlet-series coefficient. -/
theorem diagonalRankFunction_product (N j : ℕ) (s z : ℂ) :
    diagonalRankFunction N j s * conj (diagonalRankFunction N j z) =
      (if Nat.Coprime (j + 1) N then
        (mangoldt (j + 1) : ℂ) ^ 2 / (j + 1 : ℕ) ^ (1 + (s + conj z)) else 0) /
        ((1 + s) * (1 + conj z)) := by
  have hn : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show j + 1 ≠ 0 by omega)
  have hc : (Real.sqrt (diagonalCoefficient N j) : ℂ) ^ 2 = (diagonalCoefficient N j : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt (diagonalCoefficient_nonneg N j)]
  rw [diagonalRankFunction, diagonalRankFunction, map_mul, conj_ofReal, diagonalVector_conj _ (by omega)]
  unfold diagonalVector
  calc
    _ = ((Real.sqrt (diagonalCoefficient N j) : ℂ) ^ 2 *
      ((j + 1 : ℕ) : ℂ) ^ (-s) * ((j + 1 : ℕ) : ℂ) ^ (-conj z)) /
        ((1 + s) * (1 + conj z)) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ = _ := by
      rw [hc]
      congr 1
      unfold diagonalCoefficient
      split_ifs with h
      · rw [ofReal_div, ofReal_pow, ofReal_natCast]
        rw [Complex.cpow_neg, Complex.cpow_neg,
          Complex.cpow_add _ _ hn, Complex.cpow_one, Complex.cpow_add _ _ hn]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp

/-- The actual diagonal kernel is the pointwise sum of its positive rank-one kernels. -/
theorem diagonalKernel_rankSeries (N : ℕ) (s z : ℂ) (hsz : 0 < (s + conj z).re) :
    diagonalSeries N (s + conj z) / ((1 + s) * (1 + conj z)) =
      ∑' j, diagonalRankFunction N j s * conj (diagonalRankFunction N j z) := by
  have hs : Summable (fun n : ℕ => if 0 < n ∧ Nat.Coprime n N then
      (mangoldt n : ℂ) ^ 2 / (n : ℂ) ^ (1 + (s + conj z)) else 0) := by
    apply Summable.of_norm
    simpa only [apply_ite norm, norm_zero] using diagonalSeries_summable N hsz
  have heq : diagonalSeries N (s + conj z) = ∑' j : ℕ,
      if Nat.Coprime (j + 1) N then
        (mangoldt (j + 1) : ℂ) ^ 2 / (j + 1 : ℕ) ^ (1 + (s + conj z)) else 0 := by
    unfold diagonalSeries
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.not_lt_zero, false_and, ite_false, zero_add, Nat.succ_pos, true_and]
  rw [heq, ← tsum_div_const]
  exact tsum_congr (fun j => (diagonalRankFunction_product N j s z).symm)

/-- The constructed diagonal rank-one operator realizes the original boundary integral action. -/
theorem diagonalRankOperator_represents {a : ℝ} (ha : a < beta) (ha0 : 0 < a)
    (N : ℕ) [NeZero N] :
    RepresentsKernel ha N
      (fun s z => diagonalSeries N (s + conj z) / ((1 + s) * (1 + conj z)))
      (diagonalRankOperator (a := a) N) := by
  apply hardyRankOneSeries_represents ha N (diagonalRankVector N) (diagonalRankFunction N) _
    (diagonalRankVector_summable ha ha0 N)
    (fun j s hs => diagonalRankFunction_fourierLaplace ha ha0.le N j s hs)
    (fun j => (diagonalRankFunction_boundary ha ha0.le N j).1)
    (fun j => (diagonalRankFunction_boundary ha ha0.le N j).2)
  · intro s hs t
    apply diagonalKernel_rankSeries
    simp only [add_re, conj_re, line, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    linarith [hs.1]
  · intro s hs t
    apply diagonalKernel_rankSeries
    simp only [add_re, conj_re, line, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    have hb : 0 < beta := by norm_num [beta]
    linarith [hs.1]

/-- The paper's choice-based diagonal operator is exactly its positive rank-one expansion. -/
theorem diagonalOperator_eq_rankSeries {a : ℝ} (ha : a < beta) (ha0 : 0 < a)
    (N : ℕ) [NeZero N] : diagonalOperator ha N = diagonalRankOperator (a := a) N :=
  kernelOperator_eq_of_represents ha N (diagonalRankOperator_represents ha ha0 N)

/-- Positive trace class and the exact trace formula for the original diagonal operator. -/
theorem diagonalOperator_positiveTraceClass {a : ℝ} (ha : a < beta) (ha0 : 0 < a)
    (N : ℕ) [NeZero N] :
    IsPositiveTraceClass (diagonalOperator ha N) ∧
      positiveTrace (diagonalOperator ha N) =
        Real.pi / (1 + a) * (∑' j, diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * a)) +
        Real.pi / (1 + beta) * (∑' j, diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * beta)) := by
  rw [diagonalOperator_eq_rankSeries ha ha0 N]
  exact diagonalRankOperator_positiveTraceClass ha ha0 N

end ConditionalGoldbach
