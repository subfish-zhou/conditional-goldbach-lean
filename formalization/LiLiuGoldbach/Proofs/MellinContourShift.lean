import LiLiuGoldbach.Proofs.MellinBasic

/-! Contour shifting on a closed vertical strip with integrable boundary lines. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma verticalMellin_eq_of_horizontal_tendsto (f : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ z : ℂ, z.re ∈ Icc a b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f (line a t)))
    (hb : Integrable (fun t : ℝ => f (line b t)))
    (hbot : Tendsto (fun T : ℝ => ∫ x in a..b, f (line x (-T))) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x in a..b, f (line x T)) atTop (𝓝 0)) :
    verticalMellin a f = verticalMellin b f := by
  have hrect (T : ℝ) :
      (∫ x in a..b, f (line x (-T))) - (∫ x in a..b, f (line x T)) +
        I * (∫ y in -T..T, f (line b y)) - I * (∫ y in -T..T, f (line a y)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (line a (-T)) (line b T) (by
        intro z hz
        apply (hd z ?_).differentiableWithinAt
        simpa only [line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_self, add_zero, uIcc_of_le hab, mem_preimage] using hz.1)
    simpa only [line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self, add_zero, add_im, mul_im, mul_one, zero_add,
      smul_eq_mul] using h
  have hla := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hlb := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hh := ((hbot.sub htop).add (hlb.const_mul I)).sub (hla.const_mul I)
  have heq : (0 : ℂ) - 0 + I * (∫ y : ℝ, f (line b y)) -
      I * (∫ y : ℝ, f (line a y)) = 0 := by
    apply tendsto_nhds_unique hh
    simpa only [id_eq, hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
  have hi : (∫ y : ℝ, f (line b y)) = ∫ y : ℝ, f (line a y) := by
    apply (mul_left_cancel₀ I_ne_zero)
    simpa only [sub_self, zero_add, sub_eq_zero] using heq
  unfold verticalMellin
  rw [hi]

lemma horizontal_tendsto_of_uniform_decay (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2) :
    Tendsto (fun T : ℝ => ∫ x in a..b, f (line x T)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x in a..b, f (line x (-T))) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun T : ℝ => C * (1 + T)⁻¹ ^ 2 * |b - a|) atTop (𝓝 0) := by
    have hzero : Tendsto (fun T : ℝ => (1 + T)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa using ((hzero.pow 2).const_mul C).mul_const |b - a|
  constructor
  · apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa only [abs_of_nonneg hT] using hbound x ⟨hx.1.le, hx.2⟩ T
  · apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa only [abs_neg, abs_of_nonneg hT] using hbound x ⟨hx.1.le, hx.2⟩ (-T)

lemma verticalMellin_eq_of_uniform_decay (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hd : ∀ z : ℂ, z.re ∈ Icc a b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f (line a t)))
    (hb : Integrable (fun t : ℝ => f (line b t)))
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2) :
    verticalMellin a f = verticalMellin b f := by
  obtain ⟨htop, hbot⟩ := horizontal_tendsto_of_uniform_decay f a b C hab hbound
  exact verticalMellin_eq_of_horizontal_tendsto f a b hab hd ha hb hbot htop

lemma integrable_of_uniform_vertical_decay (f : ℂ → ℂ) (σ C : ℝ)
    (hc : Continuous (fun t : ℝ => f (line σ t)))
    (hbound : ∀ t : ℝ, ‖f (line σ t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2) :
    Integrable (fun t : ℝ => f (line σ t)) := by
  have hint : Integrable (fun t : ℝ => (1 + |t|)⁻¹ ^ 2) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
    convert h using 1
    ext t
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]
  exact (hint.const_mul C).mono' hc.aestronglyMeasurable (Eventually.of_forall hbound)

end LiLiuGoldbach16
