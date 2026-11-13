import ConditionalGoldbach.Proofs.FiniteModelSampling
import ConditionalGoldbach.Proofs.MellinModelRemovable

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach.FiniteModel

lemma regularizedModelMellin_eq (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    {w : ℂ} (hw : w ≠ 1) :
    regularizedModelMellin N φ w =
      continuedDensity N w * mellin (fun y => (signedConvolution φ y : ℂ)) w := by
  rw [regularizedModelMellin, dslope_of_ne _ hw, slope,
    signedConvolution_mellin_one φ hφ, vsub_eq_sub, sub_zero, smul_eq_mul,
    continuedDensity, riemannZeta_eq_inv_sub_mul hw]
  ring

lemma regularizedModelMellin_one (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) :
    regularizedModelMellin N φ 1 = (N : ℂ) / N.totient *
      deriv (mellin (fun y => (signedConvolution φ y : ℂ))) 1 := by
  simp only [regularizedModelMellin, riemannZeta₁_one, mul_one, dslope_same,
    singularSeries_mul_densityEuler_one N hN hpos]

lemma regularizedModelMellin_differentiableOn (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    DifferentiableOn ℂ (regularizedModelMellin N φ) {w : ℂ | 0 < w.re} := by
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hh : DifferentiableOn ℂ (mellin (fun y => (signedConvolution φ y : ℂ)))
      {w : ℂ | 0 < w.re} :=
    fun w hw => (signedConvolution_mellin_regular φ hφ w hw).2.differentiableWithinAt
  have hs := (Complex.differentiableOn_dslope (ho.mem_nhds (by norm_num : (1 : ℂ) ∈
      {w : ℂ | 0 < w.re}))).mpr hh
  exact (((differentiable_riemannZeta₁.differentiableOn).const_mul _).mul
    (densityEulerProduct_differentiableOn N)).mul hs

lemma regularizedModelMellin_differentiableAt (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ (regularizedModelMellin N φ) w := by
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (regularizedModelMellin_differentiableOn N φ hφ).differentiableAt (ho.mem_nhds hw)

lemma regularizedModelMellin_line_ae (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (σ : ℝ) :
    (fun t : ℝ => regularizedModelMellin N φ (line σ t)) =ᵐ[volume]
      (fun t : ℝ => continuedDensity N (line σ t) *
        mellin (fun y => (signedConvolution φ y : ℂ)) (line σ t)) := by
  filter_upwards [ae_iff.mpr (show volume {t : ℝ | ¬ t ≠ 0} = 0 by simp)] with t ht
  apply regularizedModelMellin_eq N φ hφ
  intro he
  have hi := congrArg Complex.im he
  simp only [line, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
    mul_one, mul_zero, add_zero, zero_add, one_im] at hi
  exact ht hi

lemma regularizedModelMellin_verticalMellin (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (σ : ℝ) :
    verticalMellin σ (regularizedModelMellin N φ) =
      verticalMellin σ (fun w => continuedDensity N w *
        mellin (fun y => (signedConvolution φ y : ℂ)) w) := by
  unfold verticalMellin
  rw [integral_congr_ae (regularizedModelMellin_line_ae N φ hφ σ)]

lemma regularizedModelMellin_initial (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => regularizedModelMellin N φ (line σ t)) ∧
    verticalMellin σ (regularizedModelMellin N φ) =
      -(modelMass φ * singularSeries N : ℝ) := by
  have he (t : ℝ) : regularizedModelMellin N φ (line σ t) =
      densitySeries N (line σ t) * mellin (fun y => (signedConvolution φ y : ℂ)) (line σ t) := by
    rw [regularizedModelMellin_eq N φ hφ (by
      intro he
      have hr := congrArg Complex.re he
      simp only [line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero, one_re] at hr
      linarith)]
    rw [densitySeries_eq_continuedDensity N hN hpos (by simpa [line] using hσ)]
  simpa only [he, verticalMellin] using density_signedConvolution_mellin_initial N hN hpos φ hφ σ hσ

end ConditionalGoldbach.FiniteModel
