module

public import ConditionalGoldbach.Proofs.SpectralDiagonalVector
public import ConditionalGoldbach.Proofs.SpectralRankOneSeries
public import ConditionalGoldbach.Proofs.SpectralL2BasisExistence
public import ConditionalGoldbach.Proofs.DensitySeries

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- The nonnegative diagonal Dirichlet coefficient, indexed without a zero integer term. -/
def diagonalCoefficient (N j : ℕ) : ℝ :=
  if Nat.Coprime (j + 1) N then mangoldt (j + 1) ^ 2 / (j + 1 : ℕ) else 0

theorem diagonalCoefficient_nonneg (N j : ℕ) : 0 ≤ diagonalCoefficient N j := by
  unfold diagonalCoefficient
  split_ifs <;> positivity

/-- Absolute Dirichlet convergence gives the exact weighted power summability needed for the trace. -/
theorem diagonalCoefficient_power_summable (N : ℕ) (x : ℝ) (hx : 0 < x) :
    Summable (fun j => diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * x)) := by
  have hs := diagonalSeries_summable N (w := (2 * x : ℝ)) (by simpa using mul_pos two_pos hx)
  have hs' := (summable_nat_add_iff 1).mpr hs
  apply hs'.congr
  intro j
  simp only [Nat.succ_pos, true_and, diagonalCoefficient]
  split_ifs with h
  · rw [norm_div, norm_pow, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, add_re, one_re, ofReal_re]
    rw [show -2 * x = -(2 * x) by ring, Real.rpow_neg (Nat.cast_nonneg _),
      Real.rpow_add (by positivity : (0 : ℝ) < (j + 1 : ℕ)), Real.rpow_one]
    ring
  · simp

/-- The square-root coefficient converts the diagonal expansion to a positive rank-one series. -/
def diagonalRankVector {a : ℝ} (N j : ℕ) : HardySpace a beta :=
  (Real.sqrt (diagonalCoefficient N j) : ℂ) • diagonalHardyVector (j + 1)

theorem diagonalRankVector_norm_sq {a : ℝ} (N j : ℕ) :
    ‖diagonalRankVector (a := a) N j‖ ^ 2 =
      diagonalCoefficient N j * ‖diagonalHardyVector (a := a) (j + 1)‖ ^ 2 := by
  simp only [diagonalRankVector, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (diagonalCoefficient_nonneg N j)]

/-- The diagonal rank-one vectors are square summable on every strictly positive strip. -/
theorem diagonalRankVector_summable {a : ℝ} (ha : a < beta) (ha0 : 0 < a) (N : ℕ) :
    Summable (fun j => ‖diagonalRankVector (a := a) N j‖ ^ 2) := by
  have h₁ := (diagonalCoefficient_power_summable N a ha0).mul_left (Real.pi / (1 + a))
  have h₂ := (diagonalCoefficient_power_summable N beta (by norm_num [beta])).mul_left
    (Real.pi / (1 + beta))
  apply (h₁.add h₂).congr
  intro j
  rw [diagonalRankVector_norm_sq, diagonalHardyVector_norm_sq ha ha0.le _ (by omega)]
  ring

/-- A concrete positive operator representing the diagonal rank-one expansion. -/
def diagonalRankOperator {a : ℝ} (N : ℕ) : HardySpace a beta →L[ℂ] HardySpace a beta :=
  ∑' j, rankOne ℂ (diagonalRankVector N j) (diagonalRankVector N j)

/-- The diagonal expansion is positive trace class, with both exact boundary contributions to its trace. -/
theorem diagonalRankOperator_positiveTraceClass {a : ℝ} (ha : a < beta) (ha0 : 0 < a) (N : ℕ) :
    IsPositiveTraceClass (diagonalRankOperator (a := a) N) ∧
      positiveTrace (diagonalRankOperator (a := a) N) =
        Real.pi / (1 + a) * (∑' j, diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * a)) +
        Real.pi / (1 + beta) * (∑' j, diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * beta)) := by
  have hv := diagonalRankVector_summable ha ha0 N
  have ht := rankOne_tsum_positiveTraceClass (diagonalRankVector (a := a) N) hv
    (Classical.choice (hardySpace_exists_nat_hilbertBasis a beta))
  refine ⟨ht.1, ht.2.trans ?_⟩
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add
    ((diagonalCoefficient_power_summable N a ha0).mul_left _)
    ((diagonalCoefficient_power_summable N beta (by norm_num [beta])).mul_left _)]
  apply tsum_congr
  intro j
  rw [diagonalRankVector_norm_sq, diagonalHardyVector_norm_sq ha ha0.le _ (by omega)]
  ring

end ConditionalGoldbach
