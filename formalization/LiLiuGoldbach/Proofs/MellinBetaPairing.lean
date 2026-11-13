import LiLiuGoldbach.Proofs.MellinBasic
import LiLiuGoldbach.Proofs.BetaIntegrals

/-! Absolute Fubini pairing for Mellin inversion, used in the Beta–Mellin identity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma measurable_complex_cpow {α : Type*} [MeasurableSpace α] (f g : α → ℂ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => f x ^ g x) := by
  simp_rw [Complex.cpow_def]
  exact Measurable.ite (hf (measurableSet_singleton 0))
    (Measurable.ite (hg (measurableSet_singleton 0)) measurable_const measurable_const)
    (Complex.continuous_exp.measurable.comp ((Complex.measurable_log.comp hf).mul hg))

lemma mellinWeight_pairing_integrable (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (g : ℝ → ℂ) (hg : Measurable g)
    (hi : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-(σ : ℂ)) * g u) (Ioi 0)) :
    Integrable (fun p : ℝ × ℝ => mellinWeight φ (line σ p.1) *
      (p.2 : ℂ) ^ (-line σ p.1) * g p.2) (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : ℝ × ℝ => mellinWeight φ (line σ p.1) *
      (p.2 : ℂ) ^ (-line σ p.1) * g p.2) := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact (mellinWeight_differentiable hφ).continuous.measurable.comp (by unfold line; fun_prop)
      · exact measurable_complex_cpow _ _ (by fun_prop) (by unfold line; fun_prop)
    · exact hg.comp measurable_snd
  apply ((mellinWeight_verticalIntegrable hφ σ).norm.mul_prod hi.norm).mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem measurableSet_Ioi)] with p hu
  rcases p with ⟨t, u⟩
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, neg_re, ofReal_re]
  simp only [line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_self, add_zero]
  exact (mul_assoc _ _ _).le

lemma mellinWeight_pairing (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (g : ℝ → ℂ) (hg : Measurable g)
    (hi : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-(σ : ℂ)) * g u) (Ioi 0)) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-line σ t) * g u) ∧
    (∫ u in Ioi (0 : ℝ), (companion φ u : ℂ) * g u) =
      verticalMellin σ (fun s => mellinWeight φ s *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-s) * g u) := by
  have hF := mellinWeight_pairing_integrable φ hφ σ g hg hi
  constructor
  · simpa only [mul_assoc, integral_const_mul] using hF.integral_prod_left
  · have hs := integral_integral_swap (f := fun t u : ℝ =>
      mellinWeight φ (line σ t) * (u : ℂ) ^ (-line σ t) * g u) hF
    simp only [← mul_assoc, integral_mul_const] at hs
    unfold verticalMellin
    simp only [mul_assoc, integral_const_mul] at hs
    rw [hs]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [mellinWeight_inversion hφ σ u hu]
    simp only [verticalMellin, mul_assoc]

lemma companion_mul_neg_half (φ : ℝ → ℝ) (u : ℝ) (hu : 0 < u) :
    (companion φ u : ℂ) * (u : ℂ)^(-1/2 : ℂ) = (φ u : ℂ) := by
  have hh : (u : ℂ)^(1/2 : ℂ) = (Real.sqrt u : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]
    congr 1
    norm_num
  have he : (-1/2 : ℂ) = -(1/2) := by ring
  rw [he, cpow_neg, hh, companion, ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne']

lemma mellin_phi_kernel_pairing (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (g : ℝ → ℂ) (hg : Measurable g)
    (hi : IntegrableOn (fun u : ℝ => (u : ℂ)^(-1/2-(σ : ℂ)) * g u) (Ioi 0)) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-line σ t) * g u) ∧
    (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * g u) =
      verticalMellin σ (fun s => mellinWeight φ s *
        ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * g u) := by
  have hp (s : ℂ) (u : ℝ) (hu : 0 < u) :
      (u : ℂ)^(-s) * ((u : ℂ)^(-1/2 : ℂ) * g u) =
        (u : ℂ)^(-1/2-s) * g u := by
    rw [← mul_assoc, ← cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
    congr 2
    ring
  have hg' : Measurable (fun u : ℝ => (u : ℂ)^(-1/2 : ℂ) * g u) :=
    (measurable_complex_cpow _ _ (by fun_prop) measurable_const).mul hg
  have hi' : IntegrableOn (fun u : ℝ => (u : ℂ)^(-(σ : ℂ)) *
      ((u : ℂ)^(-1/2 : ℂ) * g u)) (Ioi 0) := by
    apply hi.congr_fun _ measurableSet_Ioi
    intro u hu
    exact (hp σ u hu).symm
  have h := mellinWeight_pairing φ hφ σ _ hg' hi'
  have he (s : ℂ) : (∫ u in Ioi (0 : ℝ), (u : ℂ)^(-s) *
      ((u : ℂ)^(-1/2 : ℂ) * g u)) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * g u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact hp s u hu
  simp only [he] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [← mul_assoc, companion_mul_neg_half φ u hu]

end LiLiuGoldbach16
