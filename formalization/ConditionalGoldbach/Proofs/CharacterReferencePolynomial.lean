module

public import ConditionalGoldbach.Proofs.CharacterShortPolynomial
public import ConditionalGoldbach.Proofs.SpectralDiagonalBound

/-! The short smoothed polynomial has uniformly controlled odd-character mean square. -/
public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma smoothed_coefficient_norm_sq (X σ t : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖(mangoldt n : ℂ) * (n : ℂ) ^ (-(1 / 2 + line σ t)) * smoothedPerronWeight X n‖ ^ 2 =
      (mangoldt n) ^ 2 * (n : ℝ) ^ (-1 - 2 * σ) * smoothedPerronWeight X n ^ 2 := by
  rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_natCast_cpow_of_pos hn]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hp : ((n : ℝ) ^ (-(1 / 2 + line σ t)).re) ^ 2 = (n : ℝ) ^ (-1 - 2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    simp [line]
    ring
  rw [hp]
  simp only [sq_abs]

lemma smoothed_polynomial_average_bound (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (σ t : ℝ) (hσ : 0 < σ) :
    (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
      ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 ≤
        (1 + σ) * (Real.log 4 + 4) / σ ^ 2 := by
  rw [smoothed_polynomial_odd_parseval N hN hN4]
  let k : ℕ := ⌊(N : ℝ) / 2⌋₊
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have ht (n : ℕ) : (if Nat.Coprime n N then
      ‖(mangoldt n : ℂ) * (n : ℂ) ^ (-(1 / 2 + line σ t)) * smoothedPerronWeight ((N : ℝ) / 2) n‖ ^ 2 else 0) ≤
      if 0 < n then diagonalCoefficient N (n - 1) * (n : ℝ) ^ (-2 * σ) else 0 := by
    by_cases hn : 0 < n
    · rw [ite_eq_left hn]
      have he : n - 1 + 1 = n := by omega
      by_cases hc : Nat.Coprime n N
      · rw [ite_eq_left hc, smoothed_coefficient_norm_sq _ _ _ n hn]
        have hw := smoothedPerronWeight_nonneg_le_one (by linarith : 1 < (N : ℝ) / 2) n
        have hsq : smoothedPerronWeight ((N : ℝ) / 2) n ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
        calc
          _ ≤ mangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * σ) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
          _ = _ := by
            rw [show diagonalCoefficient N (n - 1) = mangoldt n ^ 2 / (n : ℝ) by
              simp [diagonalCoefficient, he, hc]]
            rw [show -1 - 2 * σ = -2 * σ - 1 by ring,
              Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]
            ring
      · simp [hc, diagonalCoefficient, he]
    · have he : n = 0 := by omega
      subst n
      simp [mangoldt]
  calc
    _ ≤ ∑ n ∈ Finset.range (k + 1), if 0 < n then diagonalCoefficient N (n - 1) * (n : ℝ) ^ (-2 * σ) else 0 :=
      Finset.sum_le_sum (fun n _ => ht n)
    _ = ∑ j ∈ Finset.range k, diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * σ) := by
      rw [Finset.sum_range_succ']
      simp
    _ ≤ ∑' j, diagonalCoefficient N j * (j + 1 : ℕ) ^ (-2 * σ) :=
      (diagonalCoefficient_power_summable N σ hσ).sum_le_tsum _
        (fun j _ => mul_nonneg (diagonalCoefficient_nonneg N j) (Real.rpow_nonneg (by positivity) _))
    _ ≤ _ := diagonalCoefficient_series_bound N σ hσ

end ConditionalGoldbach
