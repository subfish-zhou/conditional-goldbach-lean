module

public import ConditionalGoldbach.Proofs.MellinBetaPairing
public import ConditionalGoldbach.Proofs.MellinBetaInner

/-! Shared Beta–Mellin convolution proofs. The two weight classes supply
measurability, convergence, vertical integrability and the kernel pairing separately. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma mellinWeight_eq_phi_integral (φ : ℝ → ℝ) (s : ℂ) :
    mellinWeight φ s = ∫ u in Ioi (0 : ℝ), (u : ℂ)^(s-1/2) * (φ u : ℂ) := by
  unfold mellinWeight mellin
  simp only [smul_eq_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have hh : (Real.sqrt u : ℂ) = (u : ℂ)^(1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]
    congr 1
    norm_num
  rw [companion, ofReal_mul, hh, ← mul_assoc,
    ← cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
  congr 2
  ring

lemma measurable_betaIntegral {α : Type*} [MeasurableSpace α] (f g : α → ℂ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => betaIntegral (f x) (g x)) := by
  simp only [betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h : StronglyMeasurable (Function.uncurry (fun x (u : ℝ) =>
      (u : ℂ)^(f x-1) * (1-(u : ℂ))^(g x-1))) := by
    apply Measurable.stronglyMeasurable
    exact (measurable_complex_cpow _ _ (by fun_prop) ((hf.comp measurable_fst).sub measurable_const)).mul
      (measurable_complex_cpow _ _ (by fun_prop) ((hg.comp measurable_fst).sub measurable_const))
  exact h.integral_prod_right.measurable

namespace MellinConvolution

lemma difference_slice_mellin (φ : ℝ → ℝ) (σ : ℝ)
    (hpair : ∀ (g : ℝ → ℂ), Measurable g →
      IntegrableOn (fun u : ℝ => (u : ℂ)^(-1/2-(σ : ℂ)) * g u) (Ioi 0) →
      Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-line σ t) * g u) ∧
      (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * g u) =
        verticalMellin σ (fun s => mellinWeight φ s *
          ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * g u))
    (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      (r : ℂ)^(w-1/2-line σ t) * betaIntegral (1/2-line σ t) w) ∧
    (∫ u in Ioo (0 : ℝ) r, (φ u : ℂ) * (r-u : ℂ)^(w-1)) =
      verticalMellin σ (fun s => mellinWeight φ s *
        (r : ℂ)^(w-1/2-s) * betaIntegral (1/2-s) w) := by
  let g : ℝ → ℂ := (Iio r).indicator (fun u : ℝ => (r-u : ℂ)^(w-1))
  have hg : Measurable g :=
    (measurable_complex_cpow _ _ (by fun_prop) measurable_const).indicator measurableSet_Iio
  have he (s : ℂ) : (∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * g u) =
      (r : ℂ)^(w-1/2-s) * betaIntegral (1/2-s) w := by
    have hfun : (fun u : ℝ => (u : ℂ)^(-1/2-s) * g u) =
        (Iio r).indicator (fun u : ℝ => (u : ℂ)^(-1/2-s) * (r-u : ℂ)^(w-1)) := by
      ext u
      by_cases hu : u < r <;> simp [g, Set.indicator, hu]
    rw [hfun, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
    exact convolution_inner_beta_sum r hr s w
  have hd := convolution_betaDomain σ hσ hσupper (σ : ℂ) w (by simp) hw
  have hew : -1/2-(1/2-w) = w-1 := by ring
  have hi : IntegrableOn (fun u : ℝ => (u : ℂ)^(-1/2-(σ : ℂ)) * g u) (Ioi 0) := by
    have h := (beta_sum_integrable r hr (σ : ℂ) (1/2-w) hd).integrable_indicator measurableSet_Ioo
    rw [hew] at h
    apply h.integrableOn.congr_fun _ measurableSet_Ioi
    intro u hu
    change 0 < u at hu
    by_cases hur : u < r <;> simp [g, Set.indicator, hu, hur]
  have h := hpair g hg hi
  have hleft : (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * g u) =
      ∫ u in Ioo (0 : ℝ) r, (φ u : ℂ) * (r-u : ℂ)^(w-1) := by
    have hfun : (fun u : ℝ => (φ u : ℂ) * g u) =
        (Iio r).indicator (fun u : ℝ => (φ u : ℂ) * (r-u : ℂ)^(w-1)) := by
      ext u
      by_cases hu : u < r <;> simp [g, Set.indicator, hu]
    rw [hfun, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
  simpa only [he, hleft, mul_assoc, verticalMellin] using h

lemma sum_slice_mellin (φ : ℝ → ℝ) (σ : ℝ)
    (hpair : ∀ (g : ℝ → ℂ), Measurable g →
      IntegrableOn (fun u : ℝ => (u : ℂ)^(-1/2-(σ : ℂ)) * g u) (Ioi 0) →
      Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-line σ t) * g u) ∧
      (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * g u) =
        verticalMellin σ (fun s => mellinWeight φ s *
          ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * g u))
    (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      (r : ℂ)^(w-1/2-line σ t) * betaIntegral (1/2-line σ t) (1/2+line σ t-w)) ∧
    (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * (u+r : ℂ)^(w-1)) =
      verticalMellin σ (fun s => mellinWeight φ s *
        (r : ℂ)^(w-1/2-s) * betaIntegral (1/2-s) (1/2+s-w)) := by
  let g : ℝ → ℂ := fun u => (u+r : ℂ)^(w-1)
  have hg : Measurable g := measurable_complex_cpow _ _ (by fun_prop) measurable_const
  have hd := convolution_betaDomain σ hσ hσupper (σ : ℂ) w (by simp) hw
  have hew : -1/2-(1/2-w) = w-1 := by ring
  have hi : IntegrableOn (fun u : ℝ => (u : ℂ)^(-1/2-(σ : ℂ)) * g u) (Ioi 0) := by
    simpa only [g, hew] using beta_difference_integrable r hr (σ : ℂ) (1/2-w) hd
  have h := hpair g hg hi
  simpa only [g, convolution_inner_beta_difference r hr, mul_assoc, verticalMellin] using h

lemma mellin_phi_integrable (φ : ℝ → ℝ) (s : ℂ)
    (hc : MellinConvergent (fun u => (companion φ u : ℂ)) s) :
    IntegrableOn (fun u : ℝ => (u : ℂ)^(s-1/2) * (φ u : ℂ)) (Ioi 0) := by
  apply hc.congr_fun _ measurableSet_Ioi
  intro u hu
  change (u : ℂ)^(s-1) * (companion φ u : ℂ) = _
  have hh : (Real.sqrt u : ℂ) = (u : ℂ)^(1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]
    congr 1
    norm_num
  rw [companion, ofReal_mul, hh, ← mul_assoc,
    ← cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
  congr 2
  ring

lemma mellin_beta_outer_integrable (φ : ℝ → ℝ) (σ : ℝ) (w : ℂ)
    (hφm : Measurable φ) (hMm : Measurable (mellinWeight φ))
    (hMv : Integrable (fun t : ℝ => mellinWeight φ (line σ t)))
    (hc : MellinConvergent (fun u => (companion φ u : ℂ)) (w-(σ : ℂ)))
    (B : ℂ → ℂ) (hBm : Measurable (fun t : ℝ => B (line σ t)))
    (C : ℝ) (hB : ∀ t : ℝ, ‖B (line σ t)‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => mellinWeight φ (line σ p.1) *
      (p.2 : ℂ)^(w-1/2-line σ p.1) * B (line σ p.1) * (φ p.2 : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : ℝ × ℝ => mellinWeight φ (line σ p.1) *
      (p.2 : ℂ)^(w-1/2-line σ p.1) * B (line σ p.1) * (φ p.2 : ℂ)) := by
    apply Measurable.mul
    · apply Measurable.mul
      · apply Measurable.mul
        · exact hMm.comp (by unfold line; fun_prop)
        · exact measurable_complex_cpow _ _ (by fun_prop) (by unfold line; fun_prop)
      · exact hBm.comp measurable_fst
    · exact Complex.continuous_ofReal.measurable.comp (hφm.comp measurable_snd)
  apply ((hMv.norm.mul_const C).mul_prod
    (mellin_phi_integrable φ (w-(σ : ℂ)) hc).norm).mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)] with p hp
  rcases p with ⟨t,r⟩
  have he : (w-1/2-line σ t).re = (w-(σ : ℂ)-1/2).re := by simp [line]; ring
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, he]
  calc
    _ ≤ ‖mellinWeight φ (line σ t)‖ * r^((w-(σ : ℂ)-1/2).re) * C * ‖(φ r : ℂ)‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hB t) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hp.le _)))
        (norm_nonneg _)
    _ = _ := by dsimp only [line]; ring

lemma mellin_beta_outer_pairing (φ : ℝ → ℝ) (σ : ℝ) (w : ℂ)
    (hφm : Measurable φ) (hMm : Measurable (mellinWeight φ))
    (hMv : Integrable (fun t : ℝ => mellinWeight φ (line σ t)))
    (hc : MellinConvergent (fun u => (companion φ u : ℂ)) (w-(σ : ℂ)))
    (B : ℂ → ℂ) (hBm : Measurable (fun t : ℝ => B (line σ t)))
    (C : ℝ) (hB : ∀ t : ℝ, ‖B (line σ t)‖ ≤ C) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * B (line σ t)) ∧
    (∫ r in Ioi (0 : ℝ),
      verticalMellin σ (fun s => mellinWeight φ s * (r : ℂ)^(w-1/2-s) * B s) * (φ r : ℂ)) =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * B s) := by
  have hi := mellin_beta_outer_integrable φ σ w hφm hMm hMv hc B hBm C hB
  have he (s : ℂ) : (∫ r in Ioi (0 : ℝ), mellinWeight φ s *
      (r : ℂ)^(w-1/2-s) * B s * (φ r : ℂ)) = mellinWeight φ s * mellinWeight φ (w-s) * B s := by
    rw [mellinWeight_eq_phi_integral φ (w-s)]
    have hp : w-s-1/2 = w-1/2-s := by ring
    rw [hp, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with r
    ring
  constructor
  · simpa only [he] using hi.integral_prod_left
  · have hs := integral_integral_swap (f := fun t r : ℝ => mellinWeight φ (line σ t) *
      (r : ℂ)^(w-1/2-line σ t) * B (line σ t) * (φ r : ℂ)) hi
    simp only [he, integral_mul_const] at hs
    unfold verticalMellin
    rw [hs, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with r
    ring

lemma difference_convolution_slices_mellin (φ : ℝ → ℝ) (σ : ℝ)
    (hpair : ∀ (g : ℝ → ℂ), Measurable g →
      IntegrableOn (fun u : ℝ => (u : ℂ)^(-1/2-(σ : ℂ)) * g u) (Ioi 0) →
      Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-line σ t) * g u) ∧
      (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * g u) =
        verticalMellin σ (fun s => mellinWeight φ s *
          ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * g u))
    (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ)
    (hφm : Measurable φ) (hMm : Measurable (mellinWeight φ))
    (hMv : Integrable (fun t : ℝ => mellinWeight φ (line σ t)))
    (hc : MellinConvergent (fun u => (companion φ u : ℂ)) (w-(σ : ℂ))) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * betaIntegral (1/2-line σ t) w) ∧
    (∫ r in Ioi (0 : ℝ), (∫ u in Ioo (0 : ℝ) r, (φ u : ℂ) * (r-u : ℂ)^(w-1)) * (φ r : ℂ)) =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) w) := by
  have h := mellin_beta_outer_pairing φ σ w hφm hMm hMv hc (fun s => betaIntegral (1/2-s) w)
    (measurable_betaIntegral _ _ (by unfold line; fun_prop) measurable_const)
    (betaIntegral ((1/2-σ : ℝ) : ℂ) ((2*σ : ℝ) : ℂ)).re (fun t => by
      simpa [line, hw] using norm_betaIntegral_le_real (1/2-line σ t) w)
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [(difference_slice_mellin φ σ hpair hσ hσupper w hw r hr).2]

lemma sum_convolution_slices_mellin (φ : ℝ → ℝ) (σ : ℝ)
    (hpair : ∀ (g : ℝ → ℂ), Measurable g →
      IntegrableOn (fun u : ℝ => (u : ℂ)^(-1/2-(σ : ℂ)) * g u) (Ioi 0) →
      Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-line σ t) * g u) ∧
      (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * g u) =
        verticalMellin σ (fun s => mellinWeight φ s *
          ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * g u))
    (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ)
    (hφm : Measurable φ) (hMm : Measurable (mellinWeight φ))
    (hMv : Integrable (fun t : ℝ => mellinWeight φ (line σ t)))
    (hc : MellinConvergent (fun u => (companion φ u : ℂ)) (w-(σ : ℂ))) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * betaIntegral (1/2-line σ t) (1/2+line σ t-w)) ∧
    (∫ r in Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * (u+r : ℂ)^(w-1)) * (φ r : ℂ)) =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) (1/2+s-w)) := by
  have h := mellin_beta_outer_pairing φ σ w hφm hMm hMv hc (fun s => betaIntegral (1/2-s) (1/2+s-w))
    (measurable_betaIntegral _ _ (by unfold line; fun_prop) (by unfold line; fun_prop))
    (betaIntegral ((1/2-σ : ℝ) : ℂ) ((1/2-σ : ℝ) : ℂ)).re (fun t => by
      have he : (1/2+line σ t-w).re = 1/2-σ := by simp [line, hw]; ring
      have hb := norm_betaIntegral_le_real (1/2-line σ t) (1/2+line σ t-w)
      rw [he] at hb
      simpa [line] using hb)
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [(sum_slice_mellin φ σ hpair hσ hσupper w hw r hr).2]

end MellinConvolution
end ConditionalGoldbach
