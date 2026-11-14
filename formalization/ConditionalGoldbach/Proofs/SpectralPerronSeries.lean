module

public import ConditionalGoldbach.Proofs.SpectralPerronIntegral
public import ConditionalGoldbach.Proofs.CharacterShortPolynomial

/-! The smoothed Perron integral on its initial absolutely convergent line. -/
public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma perron_dirichlet_term (n : ℕ) (u v : ℂ) (b : ℂ) :
    (mangoldt n : ℂ) * b * (n : ℂ)^(-u) * (n : ℂ)^(-v) =
      (mangoldt n : ℂ) * b / (n : ℂ)^(u + v) := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldt]
  · have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [mul_assoc ((mangoldt n : ℂ) * b), ← Complex.cpow_add _ _ hnc,
      show -u + -v = -(u + v) by ring, Complex.cpow_neg, div_eq_mul_inv]

lemma smoothedPolynomial_perron_initial {N : ℕ} [NeZero N] (χ : Character N)
    {X c : ℝ} (hX : 1 < X) (hc : 0 < c) (u : ℂ) (hu : 1 < u.re + c) :
    (∫ t : ℝ, -logDerivative χ (u - 1 / 2 + line c (2 * Real.pi * t)) *
      smoothedPerronKernel X (line c (2 * Real.pi * t))) =
      smoothedDirichletPolynomial χ X u := by
  let v : ℝ → ℂ := fun t => line c (2 * Real.pi * t)
  let a : ℕ → ℂ := fun n => (mangoldt n : ℂ) * χ n * (n : ℂ)^(-u)
  let b : ℕ → ℂ := fun n => (mangoldt n : ℂ) * χ n / (n : ℂ)^(u + (c : ℂ))
  let F : ℕ → ℝ → ℂ := fun n t => a n * ((n : ℂ)^(-v t) * smoothedPerronKernel X (v t))
  have hK : Integrable (fun t => smoothedPerronKernel X (v t)) := by
    simpa only [Nat.cast_one, Complex.one_cpow, one_mul] using (perron_weight_integral hX hc 1 (by omega)).1
  have hb : Summable b := by
    have hs : 1 / 2 < (u + (c : ℂ) - 1 / 2).re := by simp; linarith
    convert summable_logDerivative_terms χ hs using 1
    funext n
    dsimp [b]
    congr 2
    ring
  have hFterm (n : ℕ) (t : ℝ) : F n t =
      ((mangoldt n : ℂ) * χ n / (n : ℂ)^(u + v t)) * smoothedPerronKernel X (v t) := by
    dsimp [F, a]
    rw [← mul_assoc, perron_dirichlet_term]
  have hFnorm (n : ℕ) (t : ℝ) : ‖F n t‖ = ‖b n‖ * ‖smoothedPerronKernel X (v t)‖ := by
    rw [hFterm, norm_mul]
    by_cases hn : n = 0
    · subst n
      simp [b, mangoldt]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      congr 1
      dsimp [b]
      rw [norm_div, norm_div, Complex.norm_natCast_cpow_of_pos hnpos,
        Complex.norm_natCast_cpow_of_pos hnpos]
      simp [v, line]
  have hFint (n : ℕ) : Integrable (F n) := by
    by_cases hn : n = 0
    · subst n
      simp [F, a, mangoldt]
    · exact (perron_weight_integral hX hc n (Nat.pos_of_ne_zero hn)).1.const_mul (a n)
  have hnormIntegral (n : ℕ) : (∫ t : ℝ, ‖F n t‖) =
      ‖b n‖ * (∫ t : ℝ, ‖smoothedPerronKernel X (v t)‖) := by
    simp_rw [hFnorm]
    rw [integral_const_mul]
  have hsumInt : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    simp_rw [hnormIntegral]
    exact hb.norm.mul_right _
  have htermIntegral (n : ℕ) : (∫ t : ℝ, F n t) = a n * (smoothedPerronWeight X n : ℂ) := by
    by_cases hn : n = 0
    · subst n
      simp [F, a, mangoldt]
    · dsimp only [F, v]
      rw [integral_const_mul, (perron_weight_integral hX hc n (Nat.pos_of_ne_zero hn)).2]
  have hsum (t : ℝ) : (∑' n, F n t) =
      -logDerivative χ (u - 1 / 2 + v t) * smoothedPerronKernel X (v t) := by
    have hs : 1 / 2 < (u - 1 / 2 + v t).re := by simp [v, line]; linarith
    simp_rw [hFterm]
    rw [tsum_mul_right, logDerivative_eq_neg_tsum χ hs, neg_neg]
    congr 2
    funext n
    congr 2
    ring
  calc
    _ = ∫ t : ℝ, ∑' n, F n t := by simp only [hsum, v]
    _ = ∑' n, ∫ t : ℝ, F n t := (integral_tsum_of_summable_integral_norm hFint hsumInt).symm
    _ = ∑' n, a n * (smoothedPerronWeight X n : ℂ) := tsum_congr htermIntegral
    _ = ∑ n ∈ Finset.range (⌊X⌋₊ + 1), a n * (smoothedPerronWeight X n : ℂ) := by
      apply tsum_eq_sum
      intro n hn
      have hn' : ⌊X⌋₊ < n := by
        simp only [Finset.mem_range] at hn
        omega
      have hXn : X < (n : ℝ) := Nat.lt_of_floor_lt hn'
      rw [smoothedPerronWeight_eq_zero_of_le hX n hXn.le, Complex.ofReal_zero, mul_zero]
    _ = _ := rfl

end ConditionalGoldbach
