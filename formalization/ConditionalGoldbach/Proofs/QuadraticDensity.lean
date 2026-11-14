module

public import ConditionalGoldbach.Definitions.Operators
public import ConditionalGoldbach.Proofs.MellinTestInversion

/-! An absolutely convergent density formula for the Mellin functional. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma functional_mellin_coefficient_integrable (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) :
    Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) * (1 + line σ t)) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : Continuous (fun t : ℝ => (N : ℂ) ^ (line σ t)) := by
    apply Continuous.const_cpow
    · unfold line
      fun_prop
    · exact Or.inl hNc
  have hbound : ∀ᵐ t : ℝ, ‖(N : ℂ) ^ (line σ t)‖ ≤ Real.rpow N σ := by
    filter_upwards [] with t
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNr]
    simp [line, Real.rpow_eq_pow]
  have hi := (derivativeWeight_mellin_verticalIntegrable φ hφ σ).bdd_mul hc.aestronglyMeasurable hbound
  convert hi using 1
  ext t
  rw [derivativeWeight_mellin φ hφ]
  dsimp [line]
  ring

lemma mellin_exponential_kernel (N : ℕ) (hN : 0 < N) (τ : ℝ) (s : ℂ) :
    (((Real.exp (-τ) / N : ℝ) : ℂ)) ^ (-s) = (N : ℂ) ^ s * Complex.exp (s * τ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < Real.exp (-τ) / N := div_pos (Real.exp_pos _) hNreal
  rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    cpow_def_of_ne_zero (by exact_mod_cast hN.ne'), ← Complex.exp_add,
    ← Complex.ofReal_natCast N, ← Complex.ofReal_log hNreal.le,
    ← Complex.ofReal_log hpos.le, Real.log_div (Real.exp_ne_zero _) hNreal.ne', Real.log_exp]
  push_cast
  congr 1
  ring

lemma functional_double_integrable {a b : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : σ ∈ Ioo a b)
    (ψ : HardySpace a b) :
    Integrable (fun p : ℝ × ℝ =>
      ((N : ℂ) ^ (line σ p.1) * mellinWeight φ (line σ p.1) * (1 + line σ p.1)) *
        ψ p.2 * Complex.exp (line σ p.1 * p.2)) := by
  let A : ℝ → ℂ := fun t => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) * (1 + line σ t)
  have hA : Integrable A := functional_mellin_coefficient_integrable N hN φ hφ σ
  have hψ := hardy_weighted_line_integrable hσ ψ
  have he : Continuous (fun p : ℝ × ℝ => Complex.exp (line σ p.1 * p.2)) := by
    unfold line
    fun_prop
  have hm := (hA.aestronglyMeasurable.comp_fst.mul
    (hardySpace_aestronglyMeasurable ψ).comp_snd).mul he.aestronglyMeasurable
  apply (hA.norm.mul_prod hψ.norm).mono' hm
  filter_upwards [] with p
  apply le_of_eq
  simp only [Pi.mul_apply, norm_mul, Complex.norm_exp, line, mul_re, add_re, ofReal_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, sub_self, add_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring


lemma functionalValue_integrable {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : σ ∈ Ioo a beta)
    (ψ : HardySpace a beta) :
    Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) *
      (1 + line σ t) * fourierLaplace ψ (line σ t)) := by
  have hF := functional_double_integrable N hN φ hφ σ hσ ψ
  have h := hF.integral_prod_left.const_mul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)
  convert h using 1
  ext t
  unfold fourierLaplace
  simp only [mul_assoc, integral_const_mul]
  ring


/-- All interchanges are absolutely convergent for every Hardy vector. -/
theorem functionalValue_density {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : σ ∈ Ioo a beta)
    (ψ : HardySpace a beta) :
    functionalValue N φ σ ψ = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
      ∫ τ : ℝ, ψ τ * (derivativeWeight φ (Real.exp (-τ) / N) : ℂ) := by
  let A : ℝ → ℂ := fun t => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) * (1 + line σ t)
  let F : ℝ → ℝ → ℂ := fun t τ => A t * ψ τ * Complex.exp (line σ t * τ)
  let K : ℂ := (2 * (Real.pi : ℂ))⁻¹
  let L : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)⁻¹
  have hF : Integrable (Function.uncurry F) := functional_double_integrable N hN φ hφ σ hσ ψ
  have hi (τ : ℝ) : K * (∫ t : ℝ, F t τ) =
      ψ τ * (derivativeWeight φ (Real.exp (-τ) / N) : ℂ) := by
    have hNu : 0 < Real.exp (-τ) / N := by positivity
    rw [derivativeWeight_mellin_inversion φ hφ σ _ hNu]
    unfold verticalMellin
    simp_rw [mellin_exponential_kernel N hN τ]
    dsimp [F, A, K]
    simp_rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  calc
    functionalValue N φ σ ψ = K * L * ∫ t : ℝ, ∫ τ : ℝ, F t τ := by
      have hinner (t : ℝ) : (∫ τ : ℝ, F t τ) =
          A t * ∫ τ : ℝ, ψ τ * Complex.exp (line σ t * τ) := by
        simp only [F, mul_assoc, integral_const_mul]
      change K * (∫ t : ℝ, A t * (L * ∫ τ : ℝ, ψ τ * Complex.exp (line σ t * τ))) = _
      simp_rw [hinner]
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring_nf
    _ = K * L * ∫ τ : ℝ, ∫ t : ℝ, F t τ := by rw [integral_integral_swap hF]
    _ = L * ∫ τ : ℝ, K * (∫ t : ℝ, F t τ) := by rw [integral_const_mul]; ring
    _ = _ := by simp_rw [hi]; rfl


theorem functionalValue_contour_independent {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ τ : ℝ)
    (hσ : σ ∈ Ioo a beta) (hτ : τ ∈ Ioo a beta) (ψ : HardySpace a beta) :
    functionalValue N φ σ ψ = functionalValue N φ τ ψ := by
  rw [functionalValue_density N hN φ hφ σ hσ, functionalValue_density N hN φ hφ τ hτ]

end ConditionalGoldbach
