module

public import ConditionalGoldbach.Proofs.MellinConvolutionTransform
public import ConditionalGoldbach.Proofs.MellinCompactPositive

/-! The exact signed Beta–Mellin relation, with the three original Beta terms. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma line_sub_line_reflection (σ : ℝ) (w : ℂ) (hw : w.re = 2*σ) (t : ℝ) :
    w-line σ t = line σ (w.im-t) := by
  apply Complex.ext <;> simp [line, hw]; ring

lemma verticalMellin_reflection (f : ℂ → ℂ) (σ : ℝ) (w : ℂ) (hw : w.re = 2*σ) :
    verticalMellin σ (fun s => f (w-s)) = verticalMellin σ f := by
  unfold verticalMellin
  simp_rw [line_sub_line_reflection σ w hw]
  rw [integral_sub_left_eq_self (fun t : ℝ => f (line σ t)) volume w.im]

lemma mellin_signedConvolution_eq (φ : ℝ → ℝ) (hφ : IsWeight φ) (w : ℂ) (hw : 0 < w.re) :
    mellin (fun y => (signedConvolution φ y : ℂ)) w =
      2 * mellin (fun y => (differenceConvolution φ y : ℂ)) w -
        mellin (fun y => (sumConvolution φ y : ℂ)) w := by
  have hC := (compact_mellin_regular (differenceConvolution φ)
    (differenceConvolution_contDiff φ hφ).continuous _ _ (differenceConvolution_support φ hφ) w hw).1
  have hJ := (compact_mellin_regular (sumConvolution φ)
    (sumConvolution_contDiff φ hφ).continuous _ _ (sumConvolution_support φ hφ) w hw).1
  simp only [MellinConvergent, smul_eq_mul] at hC hJ
  unfold mellin
  simp only [smul_eq_mul, signedConvolution, ofReal_sub, ofReal_mul, ofReal_ofNat, mul_sub]
  simp_rw [show ∀ a b : ℂ, a * (2*b) = 2*(a*b) by intros; ring]
  rw [integral_sub (hC.const_mul 2) hJ, integral_const_mul]

lemma signedConvolution_mellin_beta (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) (w : ℂ) (hw : w.re = 2*σ) :
    Integrable (fun t : ℝ => mellinWeight φ (line σ t) *
      mellinWeight φ (w-line σ t) * betaKernel (line σ t) (w-line σ t)) ∧
    mellin (fun y => (signedConvolution φ y : ℂ)) w =
      verticalMellin σ (fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaKernel s (w-s)) := by
  obtain ⟨hCi,hC⟩ := differenceConvolution_mellin_beta φ hφ σ hσ hσupper w hw
  obtain ⟨hJi,hJ⟩ := sumConvolution_mellin_beta φ hφ σ hσ hσupper w hw
  let C₁ : ℂ → ℂ := fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) w
  let C₂ : ℂ → ℂ := fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-(w-s)) w
  let J : ℂ → ℂ := fun s => mellinWeight φ s * mellinWeight φ (w-s) * betaIntegral (1/2-s) (1/2+s-w)
  change Integrable (fun t : ℝ => C₁ (line σ t)) at hCi
  change Integrable (fun t : ℝ => J (line σ t)) at hJi
  have hflip (s : ℂ) : C₂ s = C₁ (w-s) := by
    dsimp [C₁,C₂]
    rw [sub_sub_cancel]
    ring
  have hC₂i : Integrable (fun t : ℝ => C₂ (line σ t)) := by
    apply (hCi.comp_sub_left w.im).congr
    filter_upwards [] with t
    change C₁ (line σ (w.im-t)) = C₂ (line σ t)
    rw [hflip, line_sub_line_reflection σ w hw]
  have hC₂ : verticalMellin σ C₂ = mellin (fun y => (differenceConvolution φ y : ℂ)) w := by
    have hefun : C₂ = fun s => C₁ (w-s) := funext hflip
    rw [hefun, verticalMellin_reflection C₁ σ w hw]
    exact hC.symm
  have hk (s : ℂ) : mellinWeight φ s * mellinWeight φ (w-s) * betaKernel s (w-s) =
      C₁ s + C₂ s - J s := by
    dsimp [betaKernel, C₁,C₂,J]
    rw [add_sub_cancel]
    have he : (1/2 : ℂ)-(w-s) = 1/2+s-w := by ring
    rw [he]
    ring
  constructor
  · simp_rw [hk]
    exact (hCi.add hC₂i).sub hJi
  · rw [mellin_signedConvolution_eq φ hφ w (by linarith)]
    simp_rw [hk]
    unfold verticalMellin
    dsimp only
    rw [integral_sub (f := fun t : ℝ => C₁ (line σ t) + C₂ (line σ t))
      (g := fun t : ℝ => J (line σ t)) (hCi.add hC₂i) hJi,
      integral_add (f := fun t : ℝ => C₁ (line σ t)) (g := fun t : ℝ => C₂ (line σ t)) hCi hC₂i]
    have he : (2*(Real.pi : ℂ))⁻¹ *
        ((∫ t : ℝ, C₁ (line σ t)) + (∫ t : ℝ, C₂ (line σ t)) - (∫ t : ℝ, J (line σ t))) =
        verticalMellin σ C₁ + verticalMellin σ C₂ - verticalMellin σ J := by
      unfold verticalMellin
      ring
    rw [he, ← hC, hC₂, ← hJ]
    ring

end ConditionalGoldbach
