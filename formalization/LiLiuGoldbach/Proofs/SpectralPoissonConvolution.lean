import LiLiuGoldbach.Proofs.SpectralPoisson
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff FourierTransform Convolution
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

/-- The integrable even exponential whose Fourier transform is the Poisson density. -/
def poissonFourierDensity (a t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * a * |t| : ℝ))

theorem poissonFourierDensity_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (poissonFourierDensity a) := by
  have hp : 0 < 2 * Real.pi * a := by positivity
  have h₁ : IntegrableOn (poissonFourierDensity a) (Iic 0) := by
    apply (integrableOn_exp_mul_complex_Iic (a := (2 * Real.pi * a : ℝ)) (by simpa using hp) 0).congr_fun
      ?_ measurableSet_Iic
    intro x hx
    simp only [poissonFourierDensity, abs_of_nonpos (show x ≤ 0 from hx)]
    congr 1
    push_cast
    ring
  have h₂ : IntegrableOn (poissonFourierDensity a) (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi (a := -(2 * Real.pi * a : ℝ))
      (by simpa using neg_neg_of_pos hp) 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp only [poissonFourierDensity, abs_of_pos (show 0 < x from hx)]
    congr 1
    push_cast
    ring
  simpa only [Iic_union_Ioi, integrableOn_univ] using h₁.union h₂

/-- Direct evaluation of the Fourier transform by integrating the two half-lines. -/
theorem poissonFourierDensity_fourier (a : ℝ) (ha : 0 < a) (t : ℝ) :
    𝓕 (poissonFourierDensity a) t = (poissonKernelReal a t : ℂ) := by
  let r : ℝ := 2 * Real.pi * a
  have hr : 0 < r := by dsimp [r]; positivity
  let z₁ : ℂ := (r : ℂ) - (2 * Real.pi * t : ℝ) * I
  let z₂ : ℂ := -(r : ℂ) - (2 * Real.pi * t : ℝ) * I
  have hz₁ : 0 < z₁.re := by simpa [z₁] using hr
  have hz₂ : z₂.re < 0 := by simpa [z₂] using neg_neg_of_pos hr
  let f : ℝ → ℂ := fun u => Complex.exp ((-2 * Real.pi * (t * u) : ℝ) * I) * poissonFourierDensity a u
  have h₁ : EqOn f (fun u => Complex.exp (z₁ * u)) (Iic 0) := by
    intro u hu
    dsimp [f, poissonFourierDensity, z₁, r]
    rw [← Complex.exp_add, abs_of_nonpos hu]
    congr 1
    push_cast
    ring
  have h₂ : EqOn f (fun u => Complex.exp (z₂ * u)) (Ioi 0) := by
    intro u hu
    dsimp [f, poissonFourierDensity, z₂, r]
    rw [← Complex.exp_add, abs_of_pos hu]
    congr 1
    push_cast
    ring
  have hi₁ : IntegrableOn f (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hz₁ 0).congr_fun h₁.symm measurableSet_Iic
  have hi₂ : IntegrableOn f (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hz₂ 0).congr_fun h₂.symm measurableSet_Ioi
  have hi : Integrable f := by simpa only [Iic_union_Ioi, integrableOn_univ] using hi₁.union hi₂
  rw [Real.fourier_eq']
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  change (∫ u, f u) = _
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic,
    setIntegral_congr_fun measurableSet_Iic h₁, setIntegral_congr_fun measurableSet_Ioi h₂,
    integral_exp_mul_complex_Iic hz₁, integral_exp_mul_complex_Ioi hz₂]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hz₁ne : z₁ ≠ 0 := by intro h; simp [h] at hz₁
  have hz₂ne : z₂ ≠ 0 := by intro h; simp [h] at hz₂
  have hden : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)))
  unfold poissonKernelReal
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hz₁ne, hz₂ne, hpi, hden]
  dsimp [z₁, z₂, r]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- Inverse Fourier transform of the same even exponential. -/
theorem poissonFourierDensity_fourierInv (a : ℝ) (ha : 0 < a) :
    𝓕⁻ (poissonFourierDensity a) = fun t => (poissonKernelReal a t : ℂ) := by
  funext t
  rw [Real.fourierInv_eq_fourier_neg, poissonFourierDensity_fourier a ha]
  simp only [poissonKernelReal, neg_sq]

/-- Fourier inversion identifies the transform of the Poisson kernel. -/
theorem poissonKernelReal_fourier (a : ℝ) (ha : 0 < a) :
    𝓕 (fun t => (poissonKernelReal a t : ℂ)) = poissonFourierDensity a := by
  have hc : Continuous (poissonFourierDensity a) := by unfold poissonFourierDensity; fun_prop
  have hf : Integrable (𝓕 (poissonFourierDensity a)) := by
    simp only [funext (poissonFourierDensity_fourier a ha)]
    exact (poissonKernelReal_integral a ha).1.ofReal
  rw [← poissonFourierDensity_fourierInv a ha]
  exact hc.fourier_fourierInv_eq (poissonFourierDensity_integrable a ha) hf

/-- A uniform bound for the positive Poisson kernel. -/
theorem poissonKernelReal_bounds (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 ≤ poissonKernelReal a t ∧ poissonKernelReal a t ≤ 1 / (Real.pi * a) := by
  have hden : 0 < a ^ 2 + t ^ 2 := by positivity
  unfold poissonKernelReal
  constructor
  · positivity
  · apply (div_le_div_iff₀ (mul_pos Real.pi_pos hden) (mul_pos Real.pi_pos ha)).mpr
    nlinarith [sq_nonneg t, Real.pi_pos]

/-- Positive-width Poisson densities are continuous. -/
theorem poissonKernelReal_continuous (a : ℝ) (ha : 0 < a) : Continuous (poissonKernelReal a) := by
  apply continuous_const.div (continuous_const.mul (continuous_const.add (continuous_id.pow 2)))
  intro t
  exact mul_ne_zero Real.pi_ne_zero
    (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)))

/-- The Poisson semigroup law, proved using the Fourier transform and its inversion theorem. -/
theorem poissonKernelReal_convolution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realConvolution (poissonKernelReal a) (poissonKernelReal b) = poissonKernelReal (a + b) := by
  let P : ℝ → ℝ → ℂ := fun c t => (poissonKernelReal c t : ℂ)
  let C := P a ⋆[ContinuousLinearMap.mul ℂ ℂ] P b
  have hia : Integrable (P a) := (poissonKernelReal_integral a ha).1.ofReal
  have hib : Integrable (P b) := (poissonKernelReal_integral b hb).1.ofReal
  have hiC : Integrable C := hia.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hib
  have hfC : 𝓕 C = poissonFourierDensity (a + b) := by
    funext t
    rw [Real.fourier_mul_convolution_eq hia hib]
    change 𝓕 (fun u => (poissonKernelReal a u : ℂ)) t *
      𝓕 (fun u => (poissonKernelReal b u : ℂ)) t = _
    rw [poissonKernelReal_fourier a ha, poissonKernelReal_fourier b hb]
    unfold poissonFourierDensity
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hbd : BddAbove (Set.range (fun t => ‖P b t‖)) := by
    refine ⟨1 / (Real.pi * b), ?_⟩
    rintro x ⟨t, rfl⟩
    simpa only [P, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poissonKernelReal_bounds b hb t).1] using (poissonKernelReal_bounds b hb t).2
  have hcC : Continuous C := hbd.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hia (continuous_ofReal.comp (poissonKernelReal_continuous b hb))
  have hfiC : Integrable (𝓕 C) := by rw [hfC]; exact poissonFourierDensity_integrable _ (add_pos ha hb)
  have heq := hcC.fourierInv_fourier_eq hiC hfiC
  rw [hfC, poissonFourierDensity_fourierInv _ (add_pos ha hb)] at heq
  funext t
  apply Complex.ofReal_injective
  have ht := congrFun heq t
  change (poissonKernelReal (a + b) t : ℂ) = ∫ u, P a u * P b (t - u) at ht
  rw [ht]
  unfold realConvolution
  rw [← integral_complex_ofReal]
  simp only [ofReal_mul, P]

/-- Every Poisson convolution integral is absolutely convergent. -/
theorem poissonKernelReal_convolution_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (t : ℝ) : Integrable (fun u : ℝ => poissonKernelReal a u * poissonKernelReal b (t - u)) := by
  apply ((poissonKernelReal_integral a ha).1.mul_const (1 / (Real.pi * b))).mono'
    (((poissonKernelReal_continuous a ha).mul
      ((poissonKernelReal_continuous b hb).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
  filter_upwards [] with u
  change ‖poissonKernelReal a u * poissonKernelReal b (t - u)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (poissonKernelReal_bounds a ha u).1 (poissonKernelReal_bounds b hb (t - u)).1)]
  exact mul_le_mul_of_nonneg_left (poissonKernelReal_bounds b hb (t - u)).2
    (poissonKernelReal_bounds a ha u).1

/-- The complete Poisson convolution identity and comparison used in Lemma 6.4. -/
theorem lemma_6_4_poisson_convolution (ℓ : ℝ) (hℓ : 0 < ℓ) (t : ℝ) :
    Integrable (fun u : ℝ => poissonKernelReal 1 u * poissonKernelReal ℓ (t - u)) ∧
    realConvolution (poissonKernelReal 1) (poissonKernelReal ℓ) t =
      poissonKernelReal (1 + ℓ) t ∧
    poissonKernelReal (1 + ℓ) t ≤ (1 + ℓ) * poissonKernelReal 1 t := by
  refine ⟨poissonKernelReal_convolution_integrable 1 ℓ zero_lt_one hℓ t,
    congrFun (poissonKernelReal_convolution 1 ℓ zero_lt_one hℓ) t, ?_⟩
  have hpos : 0 < 1 + ℓ := by positivity
  unfold poissonKernelReal
  rw [← mul_div_assoc, mul_one]
  apply div_le_div_of_nonneg_left hpos.le (by positivity)
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  nlinarith

end LiLiuGoldbach16
