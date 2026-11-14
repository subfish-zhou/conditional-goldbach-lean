module

public import ConditionalGoldbach.Proofs.ModelContinuation

/-! Uniform boundedness of the Gamma quotient from the convergent Beta integral. -/
public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma betaIntegral_norm_bound_lower_re {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (u v : ℂ) (hu : p ≤ u.re) (hv : q ≤ v.re) :
    ‖betaIntegral u v‖ ≤
      ∫ t : ℝ in 0..1, ‖(t : ℂ) ^ ((p : ℂ) - 1) * (1 - (t : ℂ)) ^ ((q : ℂ) - 1)‖ := by
  calc
    ‖betaIntegral u v‖ ≤
        ∫ t : ℝ in 0..1, ‖(t : ℂ) ^ (u - 1) * (1 - (t : ℂ)) ^ (v - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        (Complex.betaIntegral_convergent (hp.trans_le hu) (hq.trans_le hv)).norm
        (Complex.betaIntegral_convergent (by simpa using hp) (by simpa using hq)).norm
      intro t ht
      rw [norm_mul, norm_mul]
      have h1 : 0 < 1 - t := sub_pos.mpr ht.2
      have he : 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
      rw [he, Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
        Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
        Complex.norm_cpow_eq_rpow_re_of_pos h1,
        Complex.norm_cpow_eq_rpow_re_of_pos h1]
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      exact mul_le_mul (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by linarith))
        (Real.rpow_le_rpow_of_exponent_ge h1 (by linarith [ht.1]) (by linarith))
        (Real.rpow_nonneg h1.le _) (Real.rpow_nonneg ht.1.le _)

lemma gammaQuotient_norm_beta (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 3 / 2) :
    ‖gammaQuotient s‖ =
      ‖betaIntegral ((3 / 2 - conj s) / 2) (s.re : ℂ)‖ * ‖(Gamma (s.re : ℂ))⁻¹‖ := by
  have hu : 0 < ((3 / 2 - conj s) / 2).re := by simp; linarith
  have hv : 0 < (s.re : ℂ).re := hs
  have he : (3 / 2 - conj s) / 2 + (s.re : ℂ) = (3 / 2 + s) / 2 := by
    apply Complex.ext <;> simp; ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hu hv, he, ← norm_mul]
  have hΓ : Gamma (s.re : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  rw [show Gamma ((3 / 2 - conj s) / 2) * Gamma (s.re : ℂ) /
      Gamma ((3 / 2 + s) / 2) * (Gamma (s.re : ℂ))⁻¹ =
      Gamma ((3 / 2 - conj s) / 2) / Gamma ((3 / 2 + s) / 2) by field_simp]
  rw [gammaQuotient, norm_div, norm_div]
  congr 1
  have hc : (3 / 2 - conj s) / 2 = conj ((3 / 2 - s) / 2) := by simp only [map_div₀, map_sub, map_ofNat]
  rw [hc, Complex.Gamma_conj, Complex.norm_conj]

lemma gammaQuotient_uniform_bound {a b : ℝ} (ha : 0 < a) (hb : b < 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b → ‖gammaQuotient s‖ ≤ C := by
  let p : ℝ := (3 / 2 - b) / 2
  have hp : 0 < p := by dsimp [p]; linarith
  let A : ℝ := ∫ t : ℝ in 0..1,
    ‖(t : ℂ) ^ ((p : ℂ) - 1) * (1 - (t : ℂ)) ^ ((a : ℂ) - 1)‖
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
  have hc : Continuous (fun x : ℝ => (Gamma (x : ℂ))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨A * max D 0, mul_nonneg hA (le_max_right _ _), ?_⟩
  intro s hs
  rw [gammaQuotient_norm_beta s (ha.trans_le hs.1) (hs.2.trans_lt hb)]
  apply mul_le_mul
  · apply betaIntegral_norm_bound_lower_re hp ha
    · dsimp [p]
      simp
      linarith [hs.2]
    · exact hs.1
  · exact (hD s.re hs).trans (le_max_left _ _)
  · exact norm_nonneg _
  · exact hA

end ConditionalGoldbach
