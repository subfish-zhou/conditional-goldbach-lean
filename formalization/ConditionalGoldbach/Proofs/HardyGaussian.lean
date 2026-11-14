module

public import ConditionalGoldbach.Proofs.HardyContourShift

/-! Gaussian regularization of raw strip-Hardy functions. -/
@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma rawHardy_slab_continuousOn {a b x y : ℝ} {f : ℂ → ℂ} (hf : IsRawHardy a b f)
    (hx : a < x) (hy : y < b) :
    ContinuousOn (fun p : ℝ × ℝ => f (line p.1 p.2)) (Icc x y ×ˢ univ) := by
  apply hf.1.continuousOn.comp (by unfold line; fun_prop)
  intro p hp
  change a < (line p.1 p.2).re ∧ (line p.1 p.2).re < b
  simp only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact ⟨hx.trans_le hp.1.1, hp.1.2.trans_lt hy⟩

lemma rawHardy_slab_memLp {a b x y : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : a < x) (hy : y < b) :
    MemLp (fun p : ℝ × ℝ => f (line p.1 p.2)) 2
      ((volume.restrict (Icc x y)).prod volume) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => f (line p.1 p.2))
      ((volume.restrict (Icc x y)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (rawHardy_slab_continuousOn hf hx hy).aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  obtain ⟨C, hC, hbound⟩ := rawHardy_uniform_line_bound hab hf
  apply (integrable_prod_iff (hm.norm.pow 2)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact (hbound u ⟨hx.trans_le hu.1, hu.2.trans_lt hy⟩).1
  · apply Integrable.of_bound (hm.norm.pow 2).norm.integral_prod_right' C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hnonneg : 0 ≤ ∫ t : ℝ, ‖f (line u t)‖ ^ 2 := integral_nonneg (fun t => sq_nonneg _)
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq, abs_of_nonneg hnonneg] using
      (hbound u ⟨hx.trans_le hu.1, hu.2.trans_lt hy⟩).2

lemma gaussian_real_memLp {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun t : ℝ => Real.exp (-ε * t ^ 2)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop :
    Continuous (fun t : ℝ => Real.exp (-ε * t ^ 2))).aestronglyMeasurable).mpr
  have h := integrable_exp_neg_mul_sq (show 0 < 2 * ε by positivity)
  convert h using 1
  funext t
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 1
  ring

def hardyGaussian (f : ℂ → ℂ) (ε τ : ℝ) (s : ℂ) : ℂ :=
  f s * Complex.exp ((ε : ℂ) * s ^ 2 - (τ : ℂ) * s)

lemma hardyGaussian_line_norm (f : ℂ → ℂ) (ε τ x t : ℝ) :
    ‖hardyGaussian f ε τ (line x t)‖ =
      Real.exp (ε * x ^ 2 - τ * x) * (‖f (line x t)‖ * Real.exp (-ε * t ^ 2)) := by
  simp only [hardyGaussian, norm_mul, Complex.norm_exp, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hre : (line x t ^ 2).re = x ^ 2 - t ^ 2 := by
    simp only [pow_two, Complex.mul_re, line, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rw [hre]
  simp only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

lemma hardyGaussian_line_integrable {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 < ε) (τ : ℝ) :
    Integrable (fun t : ℝ => hardyGaussian f ε τ (line x t)) := by
  have hi := ((rawHardy_line_memLp hab hf hx).norm.integrable_mul (gaussian_real_memLp hε)).const_mul
    (Real.exp (ε * x ^ 2 - τ * x))
  apply hi.mono' ((rawHardy_line_continuous hf hx).mul
    (by unfold line; fun_prop : Continuous (fun t : ℝ => Complex.exp
      ((ε : ℂ) * line x t ^ 2 - (τ : ℂ) * line x t)))).aestronglyMeasurable
  filter_upwards [] with t
  exact le_of_eq (hardyGaussian_line_norm f ε τ x t)

lemma hardyGaussian_slab_integrable {a b x y ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : a < x) (hy : y < b) (hε : 0 < ε) (τ : ℝ) :
    Integrable (fun p : ℝ × ℝ => hardyGaussian f ε τ (line p.1 p.2))
      ((volume.restrict (Icc x y)).prod volume) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => hardyGaussian f ε τ (line p.1 p.2))
      (Icc x y ×ˢ univ) := (rawHardy_slab_continuousOn hf hx hy).mul (by unfold line; fun_prop)
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => hardyGaussian f ε τ (line p.1 p.2))
      ((volume.restrict (Icc x y)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hcont.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (show ContinuousOn (fun u : ℝ => Real.exp (ε * u ^ 2 - τ * u)) (Icc x y) by fun_prop)
  have hi := ((rawHardy_slab_memLp hab hf hx hy).norm.integrable_mul
    ((gaussian_real_memLp hε).comp_snd (volume.restrict (Icc x y)))).const_mul B
  apply hi.mono' hm
  have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Icc x y)).prod volume), p.1 ∈ Icc x y := by
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with p hp
    exact hp.1
  filter_upwards [hae] with p hp
  rw [hardyGaussian_line_norm]
  exact mul_le_mul_of_nonneg_right (hB ⟨p.1, hp, rfl⟩)
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

lemma hardyGaussian_horizontal_integrable {a b x y ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hxy : x ≤ y) (hx : a < x) (hy : y < b)
    (hε : 0 < ε) (τ : ℝ) :
    Integrable (fun t : ℝ => ∫ u in x..y, hardyGaussian f ε τ (line u t)) := by
  have h := (hardyGaussian_slab_integrable hab hf hx hy hε τ).integral_prod_right
  simpa only [intervalIntegral.integral_of_le hxy, integral_Icc_eq_integral_Ioc] using h

lemma hardyGaussian_differentiableOn {a b : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (strip a b)) (ε τ : ℝ) :
    DifferentiableOn ℂ (hardyGaussian f ε τ) (strip a b) := by
  have hfactor : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((ε : ℂ) * s ^ 2 - (τ : ℂ) * s)) :=
    ((differentiable_id.pow 2).const_mul (ε : ℂ) |>.sub
      (differentiable_id.const_mul (τ : ℂ))).cexp
  exact hf.mul hfactor.differentiableOn

/-- The Gaussian-regularized inverse Laplace density is independent of the vertical line. -/
lemma hardyGaussian_vertical_integral_eq {a b x y ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hε : 0 < ε) (τ : ℝ) :
    (∫ t : ℝ, hardyGaussian f ε τ (line x t)) =
      ∫ t : ℝ, hardyGaussian f ε τ (line y t) := by
  have hIx := hardyGaussian_line_integrable hab hf hx hε τ
  have hIy := hardyGaussian_line_integrable hab hf hy hε τ
  rcases le_total x y with hxy | hyx
  · exact holomorphic_vertical_integral_eq hxy hx.1 hy.2 _
      (hardyGaussian_differentiableOn hf.1 ε τ) hIx hIy
      (hardyGaussian_horizontal_integrable hab hf hxy hx.1 hy.2 hε τ)
  · exact (holomorphic_vertical_integral_eq hyx hy.1 hx.2 _
      (hardyGaussian_differentiableOn hf.1 ε τ) hIy hIx
      (hardyGaussian_horizontal_integrable hab hf hyx hy.1 hx.2 hε τ)).symm

end ConditionalGoldbach
