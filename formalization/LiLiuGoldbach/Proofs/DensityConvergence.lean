import LiLiuGoldbach.Proofs.DensityResidue
import LiLiuGoldbach.Proofs.SingularLower

/-! Absolute convergence of the density Dirichlet series via a divisor majorant. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff LSeries.notation
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma totient_ratio_le_divisorCount (n : ℕ) (hn : 0 < n) :
    (n : ℝ)/n.totient ≤ n.divisors.card := by
  rw [totient_ratio_prod n hn, Nat.card_divisors hn.ne', Nat.cast_prod]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hf : 0 < n.factorization p := hprime.factorization_pos_of_dvd hn.ne'
      (Nat.dvd_of_mem_primeFactors hp)
    have hleft : (p : ℝ)/(p-1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    exact hleft.trans (by exact_mod_cast (show 2 ≤ n.factorization p+1 by omega))

lemma singularSeries_mul_le_divisorCount (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (k : ℕ) (hk : 0 < k) :
    singularSeries (k*N) ≤ ((N : ℝ)/N.totient) * k.divisors.card := by
  have hφk : 0 < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hk
  have hφN : 0 < (N.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hpos
  have hφ : (k.totient : ℝ) * N.totient ≤ (k*N).totient := by
    exact_mod_cast Nat.totient_super_multiplicative k N
  calc
    _ ≤ ((k*N : ℕ) : ℝ)/(k*N).totient :=
      singularSeries_upper_totient (k*N) (hN.mul_left k) (Nat.mul_pos hk hpos)
    _ ≤ ((k*N : ℕ) : ℝ)/(k.totient*N.totient : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hφk hφN) hφ
    _ = ((N : ℝ)/N.totient) * ((k : ℝ)/k.totient) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (totient_ratio_le_divisorCount k hk) (by positivity)

lemma LSeriesSummable_divisorCount {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n : ℕ => (n.divisors.card : ℂ)) w := by
  have h := (LSeriesSummable_one_iff.mpr hw).convolution (LSeriesSummable_one_iff.mpr hw)
  have he : LSeries.convolution (1 : ℕ → ℂ) 1 = fun n : ℕ => (n.divisors.card : ℂ) := by
    funext n
    rw [LSeries.convolution_def]
    simp only [Pi.one_apply, one_mul]
    rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℂ))]
    simp
  rwa [he] at h

lemma densitySeries_summable_norm (N : ℕ) (hN : Even N) (hpos : 0 < N)
    {w : ℂ} (hw : 1 < w.re) :
    Summable (fun k : ℕ => if 0 < k then ‖(singularSeries (k*N) : ℂ)/(k : ℂ)^w‖ else 0) := by
  have hmajor := (LSeriesSummable_divisorCount hw).norm.mul_left ((N : ℝ)/N.totient)
  apply hmajor.of_nonneg_of_le
  · intro k
    split_ifs <;> positivity
  · intro k
    by_cases hk : 0 < k
    · rw [ite_eq_left hk, LSeries.norm_term_eq, ite_eq_right hk.ne']
      simp only [norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (singularSeries_pos (k*N)), Complex.norm_natCast_cpow_of_pos hk]
      have hb := singularSeries_mul_le_divisorCount N hN hpos k hk
      calc
        _ ≤ (((N : ℝ)/N.totient) * k.divisors.card)/(k : ℝ)^w.re :=
          div_le_div_of_nonneg_right hb (Real.rpow_nonneg (Nat.cast_nonneg k) _)
        _ = _ := by ring
    · have hk0 : k = 0 := by omega
      subst k
      simp [LSeries.term]

theorem lemma_4_3_density_convergence (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    (∀ w : ℂ, 1 < w.re → Summable (fun k : ℕ =>
      if 0 < k then ‖(singularSeries (k * N) : ℂ) / (k : ℂ) ^ w‖ else 0)) ∧
    DifferentiableOn ℂ (continuedDensity N) {w | 0 < w.re ∧ w ≠ 1} := by
  exact ⟨fun w hw => densitySeries_summable_norm N hN (by omega) hw,
    continuedDensity_differentiableOn N⟩

end LiLiuGoldbach16
