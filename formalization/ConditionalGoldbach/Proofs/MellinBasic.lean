import ConditionalGoldbach.Proofs.Weights

/-! Mellin inversion of the paper's compact smooth companion weight. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff FourierTransform SchwartzMap
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

/-- The logarithmic-coordinate function used by Mathlib's Mellin/Fourier convention. -/
def mellinLogWeight (φ : ℝ → ℝ) (σ : ℝ) (x : ℝ) : ℂ :=
  Real.exp (-σ * x) • (companion φ (Real.exp (-x)) : ℂ)

theorem mellinLogWeight_contDiff {φ : ℝ → ℝ} (hφ : IsWeight φ) (σ : ℝ) :
    ContDiff ℝ ∞ (mellinLogWeight φ σ) := by
  unfold mellinLogWeight
  exact (Real.contDiff_exp.comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => -σ)).mul contDiff_id)).smul
    (Complex.ofRealCLM.contDiff.comp ((companion_contDiff hφ).comp
      (Real.contDiff_exp.comp contDiff_id.neg)))

theorem mellinLogWeight_hasCompactSupport {φ : ℝ → ℝ} (hφ : IsWeight φ) (σ : ℝ) :
    HasCompactSupport (mellinLogWeight φ σ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -Real.log (2 / 3)) (b := -Real.log (1 / 3)))
  intro x hx
  have hn : companion φ (Real.exp (-x)) ≠ 0 := by
    intro hzero
    exact hx (by simp [mellinLogWeight, hzero])
  have hs := companion_support_subset hφ hn
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) hs.1
  have hhi := Real.log_le_log (Real.exp_pos (-x)) hs.2
  rw [Real.log_exp] at hlo hhi
  constructor <;> linarith

theorem mellinWeight_convergent {φ : ℝ → ℝ} (hφ : IsWeight φ) (s : ℂ) :
    MellinConvergent (fun u => (companion φ u : ℂ)) s := by
  have hsupp : Function.support (fun u : ℝ => (u : ℂ) ^ (s - 1) *
      (companion φ u : ℂ)) ⊆ Icc (1 / 3 : ℝ) (2 / 3) := by
    intro u hu
    apply companion_support_subset hφ
    intro hzero
    exact hu (by simp [hzero])
  change IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * (companion φ u : ℂ)) (Ioi 0)
  apply Integrable.integrableOn
  apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
  apply ContinuousOn.integrableOn_Icc
  intro u hu
  have hu0 : u ≠ 0 := by linarith [hu.1]
  exact ((Complex.continuousAt_ofReal_cpow_const u (s - 1) (Or.inr hu0)).mul
    (Complex.continuous_ofReal.continuousAt.comp (companion_contDiff hφ).continuous.continuousAt)).continuousWithinAt

theorem mellinWeight_verticalIntegrable {φ : ℝ → ℝ} (hφ : IsWeight φ) (σ : ℝ) :
    VerticalIntegrable (mellinWeight φ) σ := by
  let g := (mellinLogWeight_hasCompactSupport hφ σ).toSchwartzMap
    (mellinLogWeight_contDiff hφ σ)
  have hF : Integrable (𝓕 (fun x => mellinLogWeight φ σ x)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).integrable
  have h2π : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hscaled := hF.comp_mul_right' h2π
  simpa only [VerticalIntegrable, mellinWeight, mellin_eq_fourier, add_re, ofReal_re,
    mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, add_im,
    mul_im, mul_one, zero_add, mellinLogWeight, div_eq_mul_inv] using hscaled

theorem mellinWeight_inversion {φ : ℝ → ℝ} (hφ : IsWeight φ) (σ u : ℝ) (hu : 0 < u) :
    (companion φ u : ℂ) =
      verticalMellin σ (fun s => mellinWeight φ s * (u : ℂ) ^ (-s)) := by
  have h := mellinInv_mellin_eq σ (fun u => (companion φ u : ℂ)) hu
    (mellinWeight_convergent hφ σ) (mellinWeight_verticalIntegrable hφ σ)
    (Complex.continuous_ofReal.continuousAt.comp (companion_contDiff hφ).continuous.continuousAt)
  rw [← h]
  simp only [mellinInv, verticalMellin, mellinWeight, line, smul_eq_mul]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div, Complex.ofReal_inv]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => mul_comm _ _)


theorem mellinWeight_inversion_integrable {φ : ℝ → ℝ} (hφ : IsWeight φ)
    (σ u : ℝ) (hu : 0 < u) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) * (u : ℂ) ^ (-line σ t)) := by
  have hpow : Continuous (fun t : ℝ => (u : ℂ) ^ (-line σ t)) := by
    apply Continuous.const_cpow
    · unfold line
      fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hu.ne')
  have hb : ∀ᵐ t : ℝ, ‖(u : ℂ) ^ (-line σ t)‖ ≤ Real.rpow u (-σ) := by
    filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp [line]
  simpa only [line, mul_comm] using
    (mellinWeight_verticalIntegrable hφ σ).bdd_mul hpow.aestronglyMeasurable hb


theorem mellinWeight_differentiable {φ : ℝ → ℝ} (hφ : IsWeight φ) :
    Differentiable ℂ (mellinWeight φ) := by
  have hc : Continuous (fun u : ℝ => (companion φ u : ℂ)) :=
    Complex.continuous_ofReal.comp (companion_contDiff hφ).continuous
  have htop : (fun u : ℝ => (companion φ u : ℂ)) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (2 / 3 : ℝ)] with u hu
    have hz : companion φ u = 0 := by
      by_contra hn
      exact (not_lt_of_ge (companion_support_subset hφ hn).2) hu
    simp [hz]
  have hbot : (fun u : ℝ => (companion φ u : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num))] with u hu
    have hz : companion φ u = 0 := by
      by_contra hn
      exact (not_lt_of_ge (companion_support_subset hφ hn).1) hu
    simp [hz]
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hc.locallyIntegrable.locallyIntegrableOn _)
  · exact htop.trans_isBigO (Asymptotics.isBigO_zero _ _)
  · linarith
  · exact hbot.trans_isBigO (Asymptotics.isBigO_zero _ _)
  · linarith

end ConditionalGoldbach
