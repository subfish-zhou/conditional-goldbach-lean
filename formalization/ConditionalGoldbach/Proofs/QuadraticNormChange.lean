module

public import ConditionalGoldbach.Proofs.QuadraticRiesz

/-! The real-variable change of variables in the exact functional norm. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma hardyWeight_inverse_exp (a b τ : ℝ) :
    (hardyWeight a b τ)⁻¹ =
      Real.rpow (Real.exp (-τ)) (2 * a) /
        (1 + Real.rpow (Real.exp (-τ)) (-2 * (b - a))) := by
  have h₁ : Real.rpow (Real.exp (-τ)) (2 * a) = (Real.exp (2 * a * τ))⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_neg]
    congr 1
    ring
  have h₂ : Real.rpow (Real.exp (-τ)) (-2 * (b - a)) =
      Real.exp (2 * b * τ) / Real.exp (2 * a * τ) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_sub]
    congr 1
    ring
  rw [h₁, h₂]
  unfold hardyWeight
  have ha := Real.exp_ne_zero (2 * a * τ)
  have hab : Real.exp (2 * a * τ) + Real.exp (2 * b * τ) ≠ 0 := by positivity
  field_simp

lemma normFunctional_density_integral (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ) (a : ℝ) :
    normFunctional N φ a = (2 * Real.pi)⁻¹ * ∫ τ : ℝ,
      derivativeWeight φ (Real.exp (-τ) / N) ^ 2 / hardyWeight a beta τ := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let g : ℝ → ℝ := fun τ => Real.exp (-τ) / N
  have himage : g '' univ = Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨τ, _, rfl⟩
      exact div_pos (Real.exp_pos _) hNr
    · intro hu
      refine ⟨-Real.log (N * u), mem_univ _, ?_⟩
      dsimp [g]
      rw [neg_neg, Real.exp_log (mul_pos hNr hu)]
      field_simp
  have hinj : InjOn g univ := by
    intro τ₁ _ τ₂ _ h
    dsimp [g] at h
    have := Real.exp_injective ((div_left_inj' hNr.ne').1 h)
    linarith
  have hderiv : ∀ τ ∈ univ, HasDerivWithinAt g (-Real.exp (-τ) / N) univ τ := by
    intro τ _
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-τ)) τ := by
      simpa only [mul_neg_one, Function.comp_def] using
        (Real.hasDerivAt_exp (-τ)).comp τ (hasDerivAt_neg τ)
    exact (hexp.div_const (N : ℝ)).hasDerivWithinAt
  unfold normFunctional
  congr 1
  rw [← himage, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj]
  simp only [Measure.restrict_univ, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with τ
  have hu : 0 < g τ := div_pos (Real.exp_pos _) hNr
  have hNu : (N : ℝ) * g τ = Real.exp (-τ) := by dsimp [g]; field_simp
  have habs : |-Real.exp (-τ) / (N : ℝ)| = g τ := by
    rw [neg_div, abs_neg, abs_of_pos hu]
  rw [habs, hNu, div_eq_mul_inv (derivativeWeight φ (g τ) ^ 2), hardyWeight_inverse_exp]
  dsimp [g]
  field_simp

end ConditionalGoldbach
