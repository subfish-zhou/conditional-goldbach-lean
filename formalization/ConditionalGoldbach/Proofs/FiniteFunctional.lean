import ConditionalGoldbach.Proofs.FiniteMellin
import ConditionalGoldbach.Proofs.QuadraticRiesz

/-! An absolutely convergent density formula for the Mellin functional. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

def finiteFunctionalValue {a b : ℝ} (N : ℕ) (f : ℝ → ℝ) (σ : ℝ)
    (ψ : HardySpace a b) : ℂ := verticalMellin σ (fun s =>
      (N : ℂ)^s * mellin (fun u => (f u : ℂ)) s * (1+s) * fourierLaplace ψ s)


lemma finite_functional_mellin_coefficient_integrable (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (A B : ℝ)
    (hsupp : Function.support φ ⊆ Icc A B) (σ : ℝ) (hσ0 : 0 < σ) :
    Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellin (fun u => (φ u : ℂ)) (line σ t) * (1 + line σ t)) := by
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
  have hi := (compact_mellin_finite_verticalIntegrable (mellinD φ)
    (mellinD_contDiff_finite 2 hφ) A B (mellinD_support_Icc hsupp) σ hσ0).bdd_mul hc.aestronglyMeasurable hbound
  convert hi using 1
  ext t
  rw [mellinD_transform_finite φ (hφ.of_le (by norm_num)) A B hsupp _ (by simpa [line] using hσ0)]
  dsimp [line]
  ring

lemma finite_functional_double_integrable {a b : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (A B : ℝ)
    (hsupp : Function.support φ ⊆ Icc A B) (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ ∈ Ioo a b)
    (ψ : HardySpace a b) :
    Integrable (fun p : ℝ × ℝ =>
      ((N : ℂ) ^ (line σ p.1) * mellin (fun u => (φ u : ℂ)) (line σ p.1) * (1 + line σ p.1)) *
        ψ p.2 * Complex.exp (line σ p.1 * p.2)) := by
  let M : ℝ → ℂ := fun t => (N : ℂ) ^ (line σ t) * mellin (fun u => (φ u : ℂ)) (line σ t) * (1 + line σ t)
  have hA : Integrable M := finite_functional_mellin_coefficient_integrable N hN φ hφ A B hsupp σ hσ0
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


lemma finiteFunctionalValue_integrable {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (A B : ℝ)
    (hsupp : Function.support φ ⊆ Icc A B) (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ ∈ Ioo a beta)
    (ψ : HardySpace a beta) :
    Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellin (fun u => (φ u : ℂ)) (line σ t) *
      (1 + line σ t) * fourierLaplace ψ (line σ t)) := by
  have hF := finite_functional_double_integrable N hN φ hφ A B hsupp σ hσ0 hσ ψ
  have h := hF.integral_prod_left.const_mul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)
  convert h using 1
  ext t
  unfold fourierLaplace
  simp only [mul_assoc, integral_const_mul]
  ring


/-- All interchanges are absolutely convergent for every Hardy vector. -/
theorem finiteFunctionalValue_density {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (A B : ℝ)
    (hsupp : Function.support φ ⊆ Icc A B) (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ ∈ Ioo a beta)
    (ψ : HardySpace a beta) :
    finiteFunctionalValue N φ σ ψ = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
      ∫ τ : ℝ, ψ τ * (mellinD φ (Real.exp (-τ) / N) : ℂ) := by
  let M : ℝ → ℂ := fun t => (N : ℂ) ^ (line σ t) * mellin (fun u => (φ u : ℂ)) (line σ t) * (1 + line σ t)
  let F : ℝ → ℝ → ℂ := fun t τ => M t * ψ τ * Complex.exp (line σ t * τ)
  let K : ℂ := (2 * (Real.pi : ℂ))⁻¹
  let L : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)⁻¹
  have hF : Integrable (Function.uncurry F) := finite_functional_double_integrable N hN φ hφ A B hsupp σ hσ0 hσ ψ
  have hi (τ : ℝ) : K * (∫ t : ℝ, F t τ) =
      ψ τ * (mellinD φ (Real.exp (-τ) / N) : ℂ) := by
    have hNu : 0 < Real.exp (-τ) / N := by positivity
    rw [compact_mellin_finite_inversion (mellinD φ) (mellinD_contDiff_finite 2 hφ)
      A B (mellinD_support_Icc hsupp) σ hσ0 _ hNu]
    unfold verticalMellin
    simp_rw [mellinD_transform_finite φ (hφ.of_le (by norm_num)) A B hsupp
      (line σ _) (by simpa [line] using hσ0)]
    simp_rw [mellin_exponential_kernel N hN τ]
    dsimp [F, M, K]
    simp_rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  calc
    finiteFunctionalValue N φ σ ψ = K * L * ∫ t : ℝ, ∫ τ : ℝ, F t τ := by
      have hinner (t : ℝ) : (∫ τ : ℝ, F t τ) =
          M t * ∫ τ : ℝ, ψ τ * Complex.exp (line σ t * τ) := by
        simp only [F, mul_assoc, integral_const_mul]
      change K * (∫ t : ℝ, M t * (L * ∫ τ : ℝ, ψ τ * Complex.exp (line σ t * τ))) = _
      simp_rw [hinner]
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = K * L * ∫ τ : ℝ, ∫ t : ℝ, F t τ := by rw [integral_integral_swap hF]
    _ = L * ∫ τ : ℝ, K * (∫ t : ℝ, F t τ) := by rw [integral_const_mul]; ring
    _ = _ := by simp_rw [hi]; rfl


lemma finite_derivativeDensity_hasCompactSupport (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (A B : ℝ) (hA : 0 < A) (hsupp : Function.support φ ⊆ Icc A B) :
    HasCompactSupport (fun τ : ℝ => mellinD φ (Real.exp (-τ)/N)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -Real.log (B*N)) (b := -Real.log (A*N)))
  intro τ hτ
  have hs := mellinD_support_Icc hsupp hτ
  have hlo := (le_div_iff₀ hNr).1 hs.1
  have hhi := (div_le_iff₀ hNr).1 hs.2
  have hl := Real.log_le_log (mul_pos hA hNr) hlo
  have hr := Real.log_le_log (Real.exp_pos (-τ)) hhi
  rw [Real.log_exp] at hl hr
  constructor <;> linarith

lemma finite_functional_riesz_exists {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (A B : ℝ)
    (hA : 0 < A) (hsupp : Function.support φ ⊆ Icc A B) :
    ∃ v : HardySpace a beta, ∀ σ : ℝ, 0 < σ → σ ∈ Ioo a beta → ∀ ψ,
      finiteFunctionalValue N φ σ ψ = paperInner ψ v := by
  let c : ℝ := (Real.sqrt (2*Real.pi))⁻¹
  let g : ℝ → ℝ := fun τ => c*mellinD φ (Real.exp (-τ)/N)
  have hg : Continuous g := by
    apply Continuous.const_mul
    apply (mellinD_contDiff_finite 2 hφ).continuous.comp
    fun_prop
  have hgs : HasCompactSupport g :=
    (finite_derivativeDensity_hasCompactSupport N hN φ A B hA hsupp).mul_left
  refine ⟨weightedTestVector a beta g hg hgs, ?_⟩
  intro σ hσ0 hσ ψ
  rw [weightedTestVector_pairing,finiteFunctionalValue_density N hN φ hφ A B hsupp σ hσ0 hσ]
  dsimp [g,c]
  push_cast
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with τ
  ring

end ConditionalGoldbach
