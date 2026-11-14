module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.MellinInversion
public import ConditionalGoldbach.Proofs.MellinDifferentiation

/-! Mellin inversion also applies to signed derivative weights. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff FourierTransform SchwartzMap
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma mellin_test_convergent (f : ℝ → ℝ) (hf : Continuous f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (s : ℂ) :
    MellinConvergent (fun u => (f u : ℂ)) s := by
  have hsupport : Function.support (fun u : ℝ => (u : ℂ) ^ (s - 1) * (f u : ℂ)) ⊆
      Icc (1 / 3 : ℝ) (2 / 3) := by
    intro u hu
    apply hs
    intro hzero
    exact hu (by simp [hzero])
  change IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * (f u : ℂ)) (Ioi 0)
  apply Integrable.integrableOn
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply ContinuousOn.integrableOn_Icc
  intro u hu
  have hu0 : u ≠ 0 := by linarith [hu.1]
  exact ((Complex.continuousAt_ofReal_cpow_const u (s - 1) (Or.inr hu0)).mul
    (Complex.continuous_ofReal.continuousAt.comp hf.continuousAt)).continuousWithinAt

lemma mellin_test_verticalIntegrable (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (σ : ℝ) :
    VerticalIntegrable (mellin (fun u => (f u : ℂ))) σ := by
  let g : ℝ → ℂ := fun x => Real.exp (-σ * x) • (f (Real.exp (-x)) : ℂ)
  have hg : ContDiff ℝ ∞ g := by
    exact (Real.contDiff_exp.comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => -σ)).mul contDiff_id)).smul
      (Complex.ofRealCLM.contDiff.comp (hf.comp (Real.contDiff_exp.comp contDiff_id.neg)))
  have hgs : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -Real.log (2 / 3)) (b := -Real.log (1 / 3)))
    intro x hx
    have hn : f (Real.exp (-x)) ≠ 0 := by intro hz; exact hx (by simp [g, hz])
    have h := hs hn
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) h.1
    have hr := Real.log_le_log (Real.exp_pos (-x)) h.2
    rw [Real.log_exp] at hl hr
    constructor <;> linarith
  let G := hgs.toSchwartzMap hg
  have hF : Integrable (𝓕 g) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 G).integrable
  have hscaled := hF.comp_mul_right' (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  simpa only [VerticalIntegrable, mellin_eq_fourier, add_re, ofReal_re,
    mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, add_im,
    mul_im, mul_one, zero_add, g, div_eq_mul_inv] using hscaled

lemma mellin_test_inversion (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (σ u : ℝ) (hu : 0 < u) :
    (f u : ℂ) = verticalMellin σ (fun s => mellin (fun u => (f u : ℂ)) s * (u : ℂ) ^ (-s)) := by
  have h := mellinInv_mellin_eq σ (fun u => (f u : ℂ)) hu
    (mellin_test_convergent f hf.continuous hs σ) (mellin_test_verticalIntegrable f hf hs σ)
    (Complex.continuous_ofReal.continuousAt.comp hf.continuous.continuousAt)
  rw [← h]
  simp only [mellinInv, verticalMellin, line, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_ofNat, one_div, Complex.ofReal_inv]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => mul_comm _ _)

lemma derivativeWeight_contDiff (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ContDiff ℝ ∞ (derivativeWeight φ) :=
  mellinD_contDiff (companion_contDiff hφ)

lemma derivativeWeight_mellin_verticalIntegrable (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) :
    VerticalIntegrable (mellin (fun u => (derivativeWeight φ u : ℂ))) σ :=
  mellin_test_verticalIntegrable _ (derivativeWeight_contDiff φ hφ) (derivativeWeight_support_subset hφ) σ

lemma derivativeWeight_mellin_inversion (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ u : ℝ) (hu : 0 < u) :
    (derivativeWeight φ u : ℂ) = verticalMellin σ (fun s =>
      (1 + s) * mellinWeight φ s * (u : ℂ) ^ (-s)) := by
  simpa only [derivativeWeight_mellin φ hφ] using
    mellin_test_inversion _ (derivativeWeight_contDiff φ hφ) (derivativeWeight_support_subset hφ) σ u hu

end ConditionalGoldbach
