module

public import ConditionalGoldbach.Proofs.MellinBetaPairing
public import ConditionalGoldbach.Proofs.MellinBetaConvolutionCore

/-! Convolution slices and their absolutely convergent Beta–Mellin inversions. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma difference_slice_mellin (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      (r : ℂ)^(w-1/2-line σ t) * betaIntegral (1/2-line σ t) w) ∧
    (∫ u in Ioo (0 : ℝ) r, (φ u : ℂ) * (r-u : ℂ)^(w-1)) =
      verticalMellin σ (fun s => mellinWeight φ s *
        (r : ℂ)^(w-1/2-s) * betaIntegral (1/2-s) w) :=
  MellinConvolution.difference_slice_mellin φ σ
    (mellin_phi_kernel_pairing φ hφ σ) hσ hσupper w hw r hr

lemma sum_slice_mellin (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      (r : ℂ)^(w-1/2-line σ t) * betaIntegral (1/2-line σ t) (1/2+line σ t-w)) ∧
    (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * (u+r : ℂ)^(w-1)) =
      verticalMellin σ (fun s => mellinWeight φ s *
        (r : ℂ)^(w-1/2-s) * betaIntegral (1/2-s) (1/2+s-w)) :=
  MellinConvolution.sum_slice_mellin φ σ
    (mellin_phi_kernel_pairing φ hφ σ) hσ hσupper w hw r hr

lemma mellin_phi_integrable (φ : ℝ → ℝ) (hφ : IsWeight φ) (s : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ)^(s-1/2) * (φ u : ℂ)) (Ioi 0) :=
  MellinConvolution.mellin_phi_integrable φ s (mellinWeight_convergent hφ s)

lemma mellin_beta_outer_integrable (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (w : ℂ)
    (B : ℂ → ℂ) (hBm : Measurable (fun t : ℝ => B (line σ t)))
    (C : ℝ) (hB : ∀ t : ℝ, ‖B (line σ t)‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => mellinWeight φ (line σ p.1) *
      (p.2 : ℂ)^(w-1/2-line σ p.1) * B (line σ p.1) * (φ p.2 : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) :=
  MellinConvolution.mellin_beta_outer_integrable φ σ w
    hφ.1.continuous.measurable (mellinWeight_differentiable hφ).continuous.measurable
    (mellinWeight_verticalIntegrable hφ σ) (mellinWeight_convergent hφ _) B hBm C hB

lemma mellin_beta_outer_pairing (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (w : ℂ)
    (B : ℂ → ℂ) (hBm : Measurable (fun t : ℝ => B (line σ t)))
    (C : ℝ) (hB : ∀ t : ℝ, ‖B (line σ t)‖ ≤ C) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * B (line σ t)) ∧
    (∫ r in Ioi (0 : ℝ),
      verticalMellin σ (fun s => mellinWeight φ s * (r : ℂ)^(w-1/2-s) * B s) * (φ r : ℂ)) =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * B s) :=
  MellinConvolution.mellin_beta_outer_pairing φ σ w
    hφ.1.continuous.measurable (mellinWeight_differentiable hφ).continuous.measurable
    (mellinWeight_verticalIntegrable hφ σ) (mellinWeight_convergent hφ _) B hBm C hB

lemma difference_convolution_slices_mellin (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * betaIntegral (1/2-line σ t) w) ∧
    (∫ r in Ioi (0 : ℝ), (∫ u in Ioo (0 : ℝ) r, (φ u : ℂ) * (r-u : ℂ)^(w-1)) * (φ r : ℂ)) =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) w) :=
  MellinConvolution.difference_convolution_slices_mellin φ σ
    (mellin_phi_kernel_pairing φ hφ σ) hσ hσupper w hw
    hφ.1.continuous.measurable (mellinWeight_differentiable hφ).continuous.measurable
    (mellinWeight_verticalIntegrable hφ σ) (mellinWeight_convergent hφ _)

lemma sum_convolution_slices_mellin (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * betaIntegral (1/2-line σ t) (1/2+line σ t-w)) ∧
    (∫ r in Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), (φ u : ℂ) * (u+r : ℂ)^(w-1)) * (φ r : ℂ)) =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) (1/2+s-w)) :=
  MellinConvolution.sum_convolution_slices_mellin φ σ
    (mellin_phi_kernel_pairing φ hφ σ) hσ hσupper w hw
    hφ.1.continuous.measurable (mellinWeight_differentiable hφ).continuous.measurable
    (mellinWeight_verticalIntegrable hφ σ) (mellinWeight_convergent hφ _)

end ConditionalGoldbach
