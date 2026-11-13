import LiLiuGoldbach.Proofs.FiniteModelBetaConvolution
import LiLiuGoldbach.Proofs.FiniteModelConvolution

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff Convolution
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
namespace FiniteModel

lemma weight_complex_integrable (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    Integrable (fun u => (φ u : ℂ)) :=
  Complex.ofRealCLM.integrable_comp (hφ.continuous.integrable_of_hasCompactSupport hφ.hasCompactSupport)

lemma difference_convolution_integral_pairing (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (h : ℝ → ℂ) (hi : Integrable h) :
    (∫ y : ℝ, h y * (differenceConvolution φ y : ℂ)) =
      ∫ r : ℝ, (∫ u : ℝ, (φ u : ℂ) * h (r-u)) * (φ r : ℂ) := by
  obtain ⟨B,hB⟩ := hφ.norm_bounded
  have hF : Integrable (fun p : ℝ × ℝ => h p.1 * (φ p.2 : ℂ) * (φ (p.2+p.1) : ℂ))
      (volume.prod volume) :=
    (hi.mul_prod (weight_complex_integrable φ hφ)).mul_bdd
      (by apply Continuous.aestronglyMeasurable; exact Complex.continuous_ofReal.comp (hφ.continuous.comp (by fun_prop)))
      (Eventually.of_forall (fun p => hB (p.2+p.1)))
  have hG : Integrable (fun p : ℝ × ℝ => h (p.1-p.2) * (φ p.2 : ℂ) * (φ p.1 : ℂ))
      (volume.prod volume) := by
    convert (measurePreserving_sub_prod volume volume).integrable_comp_of_integrable hF using 1
    ext p
    dsimp only [Function.comp_apply]
    rw [add_sub_cancel]
  have hsF := integral_integral_swap (f := fun y u : ℝ => h y * (φ u : ℂ) * (φ (u+y) : ℂ)) hF
  have hsG := integral_integral_swap (f := fun r u : ℝ => h (r-u) * (φ u : ℂ) * (φ r : ℂ)) hG
  calc
    _ = ∫ y : ℝ, ∫ u : ℝ, h y * (φ u : ℂ) * (φ (u+y) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [differenceConvolution_eq_real_integral φ hφ]
      rw [← integral_complex_ofReal]
      simp only [ofReal_mul, mul_assoc, integral_const_mul]
    _ = ∫ u : ℝ, ∫ y : ℝ, h y * (φ u : ℂ) * (φ (u+y) : ℂ) := hsF
    _ = ∫ u : ℝ, ∫ r : ℝ, h (r-u) * (φ u : ℂ) * (φ r : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      have ht := integral_add_right_eq_self (μ := volume) (fun r : ℝ => h (r-u) * (φ u : ℂ) * (φ r : ℂ)) u
      simpa only [add_sub_cancel_right, add_comm, add_sub_cancel_left] using ht
    _ = ∫ r : ℝ, ∫ u : ℝ, h (r-u) * (φ u : ℂ) * (φ r : ℂ) := hsG.symm
    _ = _ := by
      simp only [integral_mul_const]
      congr 1
      ext r
      congr 1
      apply integral_congr_ae
      filter_upwards [] with u
      ring

lemma sum_convolution_integral_pairing (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (h : ℝ → ℂ) (hi : Integrable h) :
    (∫ y : ℝ, h y * (sumConvolution φ y : ℂ)) =
      ∫ r : ℝ, (∫ u : ℝ, (φ u : ℂ) * h (u+r)) * (φ r : ℂ) := by
  obtain ⟨B,hB⟩ := hφ.norm_bounded
  have hF : Integrable (fun p : ℝ × ℝ => h p.1 * (φ p.2 : ℂ) * (φ (p.1-p.2) : ℂ))
      (volume.prod volume) :=
    (hi.mul_prod (weight_complex_integrable φ hφ)).mul_bdd
      (by apply Continuous.aestronglyMeasurable; exact Complex.continuous_ofReal.comp (hφ.continuous.comp (by fun_prop)))
      (Eventually.of_forall (fun p => hB (p.1-p.2)))
  have hG : Integrable (fun p : ℝ × ℝ => h (p.1+p.2) * (φ p.2 : ℂ) * (φ p.1 : ℂ))
      (volume.prod volume) := by
    convert (measurePreserving_add_prod volume volume).integrable_comp_of_integrable hF using 1
    ext p
    dsimp only [Function.comp_apply]
    rw [add_sub_cancel_right]
  have hsF := integral_integral_swap (f := fun y u : ℝ => h y * (φ u : ℂ) * (φ (y-u) : ℂ)) hF
  have hsG := integral_integral_swap (f := fun r u : ℝ => h (r+u) * (φ u : ℂ) * (φ r : ℂ)) hG
  calc
    _ = ∫ y : ℝ, ∫ u : ℝ, h y * (φ u : ℂ) * (φ (y-u) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [sumConvolution_eq_convolution φ hφ]
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [← integral_complex_ofReal]
      simp only [ofReal_mul, mul_assoc, integral_const_mul]
    _ = ∫ u : ℝ, ∫ y : ℝ, h y * (φ u : ℂ) * (φ (y-u) : ℂ) := hsF
    _ = ∫ u : ℝ, ∫ r : ℝ, h (r+u) * (φ u : ℂ) * (φ r : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      have ht := integral_sub_right_eq_self (μ := volume) (fun r : ℝ => h (r+u) * (φ u : ℂ) * (φ r : ℂ)) u
      simpa only [sub_add_cancel] using ht
    _ = ∫ r : ℝ, ∫ u : ℝ, h (r+u) * (φ u : ℂ) * (φ r : ℂ) := hsG.symm
    _ = _ := by
      simp only [integral_mul_const]
      congr 1
      ext r
      congr 1
      apply integral_congr_ae
      filter_upwards [] with u
      rw [add_comm r u, mul_comm (h (u+r)) (φ u : ℂ)]

def truncatedPositiveMellinKernel (w : ℂ) : ℝ → ℂ :=
  (Ioo (0 : ℝ) 2).indicator (fun y : ℝ => (y : ℂ)^(w-1))

lemma truncatedPositiveMellinKernel_integrable (w : ℂ) (hw : 0 < w.re) :
    Integrable (truncatedPositiveMellinKernel w) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
  exact (intervalIntegral.integrableOn_Ioo_cpow_iff (by norm_num : (0 : ℝ) < 2)).2
    (by simp only [sub_re, one_re]; linarith)

lemma mellin_eq_truncated_kernel (f : ℝ → ℝ) (A B : ℝ) (hB : B < 2)
    (hf : Function.support f ⊆ Icc A B) (w : ℂ) :
    mellin (fun y => (f y : ℂ)) w =
      ∫ y : ℝ, truncatedPositiveMellinKernel w y * (f y : ℂ) := by
  unfold mellin
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hz : f y = 0
  · simp [hz, smul_eq_mul]
  · have hs := hf hz
    have hy2 : y < 2 := hs.2.trans_lt hB
    by_cases hy : 0 < y <;> simp [truncatedPositiveMellinKernel, Set.indicator, hy, hy2, smul_eq_mul]

lemma differenceConvolution_mellin_physical (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (w : ℂ) (hw : 0 < w.re) :
    mellin (fun y => (differenceConvolution φ y : ℂ)) w =
      ∫ r in Ioi (0 : ℝ), (∫ u in Ioo (0 : ℝ) r, (φ u : ℂ) * (r-u : ℂ)^(w-1)) * (φ r : ℂ) := by
  rw [mellin_eq_truncated_kernel _ _ _ (by linarith [hφ.lower_pos,hφ.upper_lt_one] : hφ.upper-hφ.lower < 2)
    (differenceConvolution_support φ hφ),
    difference_convolution_integral_pairing φ hφ _ (truncatedPositiveMellinKernel_integrable w hw)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun r hr => by
    rw [hφ.eq_zero_of_nonpos (by simpa only [mem_Ioi, not_lt] using hr), ofReal_zero, mul_zero])]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  by_cases hzr : φ r = 0
  · simp [hzr]
  · congr 1
    rw [← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hzu : φ u = 0
    · simp [hzu, Set.indicator]
    · have hrs := hφ.mem_support_unit hzr
      have hus := hφ.mem_support_unit hzu
      have hu : 0 < u := by linarith [hus.1]
      have hru : r-u < 2 := by linarith [hrs.2, hus.1]
      by_cases hur : u < r
      · have hpos : 0 < r-u := sub_pos.mpr hur
        simp [truncatedPositiveMellinKernel, Set.indicator, hu, hur, hpos, hru, ofReal_sub]
      · have hnon : ¬0 < r-u := by linarith
        simp [truncatedPositiveMellinKernel, Set.indicator, hu, hur, hnon]

lemma sumConvolution_mellin_physical (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (w : ℂ) (hw : 0 < w.re) :
    mellin (fun y => (sumConvolution φ y : ℂ)) w =
      ∫ r in Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * (u+r : ℂ)^(w-1)) * (φ r : ℂ) := by
  rw [mellin_eq_truncated_kernel _ _ _ (by linarith [hφ.upper_lt_one] : 2*hφ.upper < 2)
    (sumConvolution_support φ hφ),
    sum_convolution_integral_pairing φ hφ _ (truncatedPositiveMellinKernel_integrable w hw)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun r hr => by
    rw [hφ.eq_zero_of_nonpos (by simpa only [mem_Ioi, not_lt] using hr), ofReal_zero, mul_zero])]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  by_cases hzr : φ r = 0
  · simp [hzr]
  · congr 1
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hzu : φ u = 0
    · simp [hzu, Set.indicator]
    · have hrs := hφ.mem_support_unit hzr
      have hus := hφ.mem_support_unit hzu
      have hu : 0 < u := by linarith [hus.1]
      have hsum : 0 < u+r ∧ u+r < 2 := by constructor <;> linarith [hrs.1, hrs.2, hus.1, hus.2]
      simp [truncatedPositiveMellinKernel, Set.indicator, hu, hsum.1, hsum.2, ofReal_add]

lemma differenceConvolution_mellin_beta (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * betaIntegral (1/2-line σ t) w) ∧
    mellin (fun y => (differenceConvolution φ y : ℂ)) w =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) w) := by
  rw [differenceConvolution_mellin_physical φ hφ w (by linarith)]
  exact difference_convolution_slices_mellin φ hφ σ hσ hσupper w hw

lemma sumConvolution_mellin_beta (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * betaIntegral (1/2-line σ t) (1/2+line σ t-w)) ∧
    mellin (fun y => (sumConvolution φ y : ℂ)) w =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) (1/2+s-w)) := by
  rw [sumConvolution_mellin_physical φ hφ w (by linarith)]
  exact sum_convolution_slices_mellin φ hφ σ hσ hσupper w hw

end FiniteModel
end LiLiuGoldbach16
