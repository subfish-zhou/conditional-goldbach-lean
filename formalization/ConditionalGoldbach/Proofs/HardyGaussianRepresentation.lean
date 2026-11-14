module

public import ConditionalGoldbach.Proofs.HardyGaussianSpace

/-! Fourier inversion identifies each Gaussian density with its holomorphic regularization. -/
public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma classical_fourier_real_rescale (g : ℝ → ℂ) {c : ℝ} (hc : c ≠ 0) (w : ℝ) :
    𝓕 (fun t : ℝ => g (c * t)) w = |c⁻¹| • 𝓕 g (w / c) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  rw [← Measure.integral_comp_mul_left
    (fun t : ℝ => Complex.exp ((-2 * Real.pi * inner ℝ t (w / c) : ℝ) * Complex.I) • g t) c]
  apply integral_congr_ae
  filter_upwards [] with t
  have he : inner ℝ (c * t) (w / c) = inner ℝ t w := by
    simp only [Real.inner_apply]
    field_simp
  rw [he]

lemma classical_fourier_const_mul (g : ℝ → ℂ) (k : ℂ) (w : ℝ) :
    𝓕 (fun t : ℝ => k * g t) w = k * 𝓕 g w := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul]
  ring

lemma fourierLaplace_of_classical_fourier_density {a b x : ℝ} (hx : x ∈ Ioo a b)
    (ψ : HardySpace a b) (g : ℝ → ℂ) (hg : Integrable g) (hgc : Continuous g)
    (hcoef : (fun τ : ℝ => (Real.exp (x * τ) : ℂ) * ψ τ) =ᵐ[volume]
      fun τ => (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * 𝓕 g (τ / (2 * Real.pi))) (t : ℝ) :
    fourierLaplace ψ (line x t) = g t := by
  let k : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)⁻¹
  let c : ℝ := (2 * Real.pi)⁻¹
  have hk : k ≠ 0 := by
    apply inv_ne_zero
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hscaled : Integrable (fun τ : ℝ => 𝓕 g (τ / (2 * Real.pi))) := by
    apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hk) _).mp
    exact (hardy_weighted_line_integrable hx ψ).congr hcoef
  have hFT : Integrable (𝓕 g) := by
    apply (integrable_comp_mul_left_iff (𝓕 g) hc).mp
    convert hscaled using 1
    funext τ
    dsimp [c]
    ring
  have hf : 𝓕 (fun τ : ℝ => (Real.exp (x * τ) : ℂ) * ψ τ) (-t / (2 * Real.pi)) =
      k * ((|c⁻¹| : ℝ) : ℂ) * 𝓕 (𝓕 g) (-t) := by
    rw [Real.fourier_congr_ae hcoef]
    have hfun : (fun τ : ℝ => (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * 𝓕 g (τ / (2 * Real.pi))) =
        (fun τ : ℝ => k * 𝓕 g (c * τ)) := by
      funext τ
      congr 2
      dsimp [c]
      ring
    rw [hfun, classical_fourier_const_mul]
    rw [classical_fourier_real_rescale (𝓕 g) hc]
    have he : (-t / (2 * Real.pi)) / c = -t := by dsimp [c]; field_simp
    rw [he, Complex.real_smul, mul_assoc]
  rw [fourierLaplace_line_eq_classical_fourier, hf,
    ← Real.fourierInv_eq_fourier_neg, hg.fourierInv_fourier_eq hFT hgc.continuousAt]
  have hnorm : k * k * ((|c⁻¹| : ℝ) : ℂ) = 1 := by
    dsimp [k, c]
    rw [inv_inv, abs_of_pos (by positivity : 0 < 2 * Real.pi),
      ← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    field_simp
  change k * (k * ((|c⁻¹| : ℝ) : ℂ) * g t) = g t
  rw [← mul_assoc, ← mul_assoc, hnorm, one_mul]

lemma hardyGaussianVector_representation_line {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 < ε) (hε' : ε ≤ 1) (t : ℝ) :
    fourierLaplace (hardyGaussianVector hab hf hε hε') (line x t) =
      hardyGaussian f ε 0 (line x t) := by
  apply fourierLaplace_of_classical_fourier_density hx _ _
    (hardyGaussian_line_integrable hab hf hx hε 0)
    ((rawHardy_line_continuous hf hx).mul (by unfold line; fun_prop))
  filter_upwards [(volume_absolutelyContinuous_hardyMeasure a b).ae_eq
    (hardyGaussianDensity_memLp hab hf hε hε').coeFn_toLp] with τ hτ
  rw [hardyGaussianVector, hτ]
  exact hardyGaussianDensity_weighted_line hab hf hx hε τ

lemma hardyGaussianVector_representation {a b ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hε : 0 < ε) (hε' : ε ≤ 1) {s : ℂ} (hs : s ∈ strip a b) :
    fourierLaplace (hardyGaussianVector hab hf hε hε') s = f s * Complex.exp ((ε : ℂ) * s ^ 2) := by
  have hline : line s.re s.im = s := Complex.re_add_im s
  have h := hardyGaussianVector_representation_line hab hf hs hε hε' s.im
  simpa only [hline, hardyGaussian, Complex.ofReal_zero, zero_mul, sub_zero] using h

end ConditionalGoldbach
