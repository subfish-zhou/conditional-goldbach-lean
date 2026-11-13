import ConditionalGoldbach.Proofs.HardyKernelMajorant
import ConditionalGoldbach.Proofs.CharacterTraceBounds
import ConditionalGoldbach.Proofs.MellinContourShift
import Mathlib.Analysis.Complex.RemovableSingularity

/-! A weighted Cauchy formula on a right half-plane, proved by removing the interior pole. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex Metric
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

def halfPlaneDifference (f : ℂ → ℂ) (z : ℂ) : ℂ := -dslope f 1 z / (z + 1)

lemma halfPlaneDifference_eq (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1) :
    halfPlaneDifference f z = (f z - f 1) / (1 - z ^ 2) := by
  rw [halfPlaneDifference, dslope_of_ne f hz, slope_def_field]
  by_cases hm : z + 1 = 0
  · have he : z = -1 := by linear_combination hm
    subst z
    norm_num
  · have hp : 1 - z ^ 2 ≠ 0 := by
      have h : (z - 1) * (z + 1) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hz) hm
      intro he
      apply h
      linear_combination -he
    field_simp [sub_ne_zero.mpr hz, hm, hp]
    ring

lemma halfPlaneDifference_differentiableAt (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (z : ℂ) (hz : 0 ≤ z.re) : DifferentiableAt ℂ (halfPlaneDifference f) z := by
  have hds : DifferentiableAt ℂ (dslope f 1) z := by
    by_cases he : z = 1
    · subst z
      have hU : {w : ℂ | 0 < w.re} ∈ 𝓝 (1 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      exact ((Complex.differentiableOn_dslope hU).mpr
        (fun w hw => (hd w hw.le).differentiableWithinAt)).differentiableAt hU
    · exact (differentiableAt_dslope_of_ne he).mpr (hd z hz)
  apply hds.neg.div (differentiableAt_id.add_const 1)
  intro he
  have hh := congrArg Complex.re he
  simp only [id_eq, add_re, one_re, zero_re] at hh
  linarith

lemma halfPlaneDifference_boundary (f : ℂ → ℂ) (t : ℝ) :
    halfPlaneDifference f (line 0 t) = (f (line 0 t) - f 1) / (1 + (t : ℂ) ^ 2) := by
  rw [halfPlaneDifference_eq f (by intro he; have := congrArg Complex.re he; simp [line] at this)]
  congr 1
  simp [line, mul_pow, Complex.I_sq]

lemma norm_line_sub_one_sq (x t : ℝ) : ‖line x t - 1‖ ^ 2 = (x - 1) ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [line]
  ring

lemma halfPlaneDifference_far_bound (f : ℂ → ℂ) (B : ℝ)
    {x : ℝ} (hx : 2 ≤ x) (t : ℝ) (hb : ‖f (line x t)‖ ≤ B) :
    ‖halfPlaneDifference f (line x t)‖ ≤ (B + ‖f 1‖) / ((x - 1) ^ 2 + t ^ 2) := by
  have hz : line x t ≠ (1 : ℂ) := by
    intro he
    have hh := congrArg Complex.re he
    simp [line] at hh
    linarith
  rw [halfPlaneDifference, dslope_of_ne f hz, slope_def_field, norm_div, norm_neg, norm_div]
  have hnum : ‖f (line x t) - f 1‖ ≤ B + ‖f 1‖ :=
    (norm_sub_le _ _).trans (add_le_add hb le_rfl)
  have hnorm : ‖line x t - 1‖ ≤ ‖line x t + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_line_sub_one_sq, add_comm (line x t) 1, norm_one_add_line_sq]
    nlinarith
  have hp : 0 < ‖line x t - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  calc
    _ ≤ (B + ‖f 1‖) / ‖line x t - 1‖ / ‖line x t + 1‖ :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (B + ‖f 1‖) / ‖line x t - 1‖ / ‖line x t - 1‖ := by
      apply div_le_div_of_nonneg_left _ hp hnorm
      exact div_nonneg ((norm_nonneg _).trans hnum) hp.le
    _ = _ := by rw [div_div, ← sq, norm_line_sub_one_sq]

lemma horizontal_tendsto_of_three_halves_decay (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hb : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (-(3/2 : ℝ))) :
    Tendsto (fun T : ℝ => ∫ x in a..b, f (line x T)) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => ∫ x in a..b, f (line x (-T))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun T : ℝ => (1 + T) ^ (-(3/2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/2)).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hmajor : Tendsto (fun T : ℝ => C * (1 + T) ^ (-(3/2 : ℝ)) * |b-a|) atTop (𝓝 0) := by
    simpa using (hpow.const_mul C).mul_const |b-a|
  constructor
  · apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa only [abs_of_nonneg hT] using hb x ⟨hx.1.le, hx.2⟩ T
  · apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa only [abs_neg, abs_of_nonneg hT] using hb x ⟨hx.1.le, hx.2⟩ (-T)

lemma halfPlaneDifference_tail_bound (f : ℂ → ℂ) {x C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    (t : ℝ) (ht : 1 ≤ |t|) :
    ‖halfPlaneDifference f (line x t)‖ ≤
      (4 * (C + ‖f 1‖)) * (1 + |t|) ^ (-(3/2 : ℝ)) := by
  have ht0 : 0 < |t| := by linarith
  have hz : line x t ≠ (1 : ℂ) := by
    intro he
    have hh := congrArg Complex.im he
    simp [line] at hh
    norm_num [hh] at ht
  rw [halfPlaneDifference, dslope_of_ne f hz, slope_def_field, norm_div, norm_neg, norm_div, div_div]
  have hn1 : |t| ≤ ‖line x t - 1‖ := by simpa [line] using Complex.abs_im_le_norm (line x t - 1)
  have hn2 : |t| ≤ ‖line x t + 1‖ := by simpa [line] using Complex.abs_im_le_norm (line x t + 1)
  have hden : (1 + |t|) ^ 2 / 4 ≤ ‖line x t - 1‖ * ‖line x t + 1‖ := by
    have hh := mul_le_mul hn1 hn2 (abs_nonneg t) (norm_nonneg _)
    nlinarith [sq_nonneg (|t| - 1)]
  have hr : 1 ≤ (1 + |t|) ^ (1/2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hnum : ‖f (line x t) - f 1‖ ≤ (C + ‖f 1‖) * (1 + |t|) ^ (1/2 : ℝ) := by
    calc
      _ ≤ ‖f (line x t)‖ + ‖f 1‖ := norm_sub_le _ _
      _ ≤ C * (1 + |t|) ^ (1/2 : ℝ) + ‖f 1‖ * (1 + |t|) ^ (1/2 : ℝ) :=
        add_le_add (hb t) (by nlinarith [norm_nonneg (f 1)])
      _ = _ := by ring
  calc
    _ ≤ ((C + ‖f 1‖) * (1 + |t|) ^ (1/2 : ℝ)) / (‖line x t - 1‖ * ‖line x t + 1‖) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((C + ‖f 1‖) * (1 + |t|) ^ (1/2 : ℝ)) / ((1 + |t|) ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [show (1 + |t|) ^ (2 : ℕ) = (1 + |t|) ^ (2 : ℝ) by rw [Real.rpow_two]]
      calc
        _ = (4 * (C + ‖f 1‖)) * ((1 + |t|) ^ (1/2 : ℝ) / (1 + |t|) ^ (2 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_sub (by positivity : 0 < 1 + |t|)]; norm_num

lemma halfPlaneDifference_strip_bound (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Icc 0 R, ∀ t : ℝ, ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖halfPlaneDifference f (line x t)‖ ≤ M * (1 + |t|) ^ (-(3/2 : ℝ)) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => halfPlaneDifference f (line p.1 p.2))
      (Icc 0 R ×ˢ Icc (-1 : ℝ) 1) := by
    intro p hp
    have hh : ContinuousAt (halfPlaneDifference f) (line p.1 p.2) :=
      (halfPlaneDifference_differentiableAt f hd (line p.1 p.2) (by simpa [line] using hp.1.1)).continuousAt
    have hl : Continuous (fun q : ℝ × ℝ => line q.1 q.2) := by unfold line; fun_prop
    exact (hh.comp (x := p) hl.continuousAt).continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  let M := max (4 * (C + ‖f 1‖)) (max K 0 * (2 : ℝ) ^ (3/2 : ℝ))
  have hM : 0 ≤ M := le_max_of_le_left (by positivity)
  refine ⟨M, hM, ?_⟩
  intro x hx t
  by_cases ht : 1 ≤ |t|
  · exact (halfPlaneDifference_tail_bound f hC (hb x hx) t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  · have ht' : t ∈ Icc (-1 : ℝ) 1 := by
      have hh := abs_lt.mp (lt_of_not_ge ht)
      exact ⟨hh.1.le, hh.2.le⟩
    have hh := hK (x,t) ⟨hx, ht'⟩
    have hp : (1 + |t|) ^ (3/2 : ℝ) ≤ (2 : ℝ) ^ (3/2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hpp : 0 < (1 + |t|) ^ (3/2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |t|), ← div_eq_mul_inv]
    apply (le_div_iff₀ hpp).mpr
    calc
      _ ≤ max K 0 * (1 + |t|) ^ (3/2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hh.trans (le_max_left _ _)) hpp.le
      _ ≤ max K 0 * (2 : ℝ) ^ (3/2 : ℝ) := mul_le_mul_of_nonneg_left hp (le_max_right _ _)
      _ ≤ M := le_max_right _ _

lemma cauchy_weight_integral {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) ∧
      (∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹) = Real.pi / a := by
  have he : (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) =
      fun t : ℝ => a⁻¹ ^ 2 * (1 + (a⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    have h1 : a ^ 2 + t ^ 2 ≠ 0 := by positivity
    have h2 : 1 + (a⁻¹ * t) ^ 2 ≠ 0 := by positivity
    field_simp [ha.ne', h1, h2]
  rw [he]
  refine ⟨(integrable_inv_one_add_mul_sq (inv_ne_zero ha.ne')).const_mul _, ?_⟩
  rw [integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr ha)]
  field_simp [ha.ne']

lemma halfPlaneDifference_line_integrable (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    {x : ℝ} (hx : 0 ≤ x) : Integrable (fun t : ℝ => halfPlaneDifference f (line x t)) := by
  obtain ⟨C, hC, hb⟩ := hg x hx
  obtain ⟨M, hM, hm⟩ := halfPlaneDifference_strip_bound f hd hx hC hb
  apply (hardy_decay_integrable.const_mul M).mono' ?_ (Eventually.of_forall (hm x ⟨hx, le_rfl⟩))
  apply Continuous.aestronglyMeasurable
  apply continuous_iff_continuousAt.mpr
  intro t
  have hh : ContinuousAt (halfPlaneDifference f) (line x t) :=
    (halfPlaneDifference_differentiableAt f hd _ (by simpa [line] using hx)).continuousAt
  exact hh.comp (show ContinuousAt (fun t : ℝ => line x t) t by unfold line; fun_prop)

lemma halfPlaneDifference_integral_eq (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ t : ℝ, halfPlaneDifference f (line 0 t)) = ∫ t : ℝ, halfPlaneDifference f (line R t) := by
  obtain ⟨C, hC, hb⟩ := hg R hR
  obtain ⟨M, hM, hm⟩ := halfPlaneDifference_strip_bound f hd hR hC hb
  obtain ⟨htop, hbot⟩ := horizontal_tendsto_of_three_halves_decay (halfPlaneDifference f) 0 R M hR hm
  have he := verticalMellin_eq_of_horizontal_tendsto (halfPlaneDifference f) 0 R hR
    (fun z hz => halfPlaneDifference_differentiableAt f hd z hz.1)
    (halfPlaneDifference_line_integrable f hd hg le_rfl)
    (halfPlaneDifference_line_integrable f hd hg hR) hbot htop
  unfold verticalMellin at he
  apply mul_left_cancel₀ (show ((2 * Real.pi : ℝ) : ℂ)⁻¹ ≠ 0 by
    apply inv_ne_zero; exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  simpa only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] using he

lemma halfPlaneDifference_integral_zero (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    (hb : ∃ R₀ B : ℝ, ∀ z : ℂ, R₀ ≤ z.re → ‖f z‖ ≤ B) :
    (∫ t : ℝ, halfPlaneDifference f (line 0 t)) = 0 := by
  obtain ⟨R₀, B, hB⟩ := hb
  have hbpos : 0 ≤ B := (norm_nonneg (f R₀)).trans (hB R₀ (by simp))
  have hbound (R : ℝ) (hR : max 2 R₀ ≤ R) :
      ‖∫ t : ℝ, halfPlaneDifference f (line R t)‖ ≤ (B + ‖f 1‖) * (Real.pi / (R-1)) := by
    have hR2 : 2 ≤ R := (le_max_left _ _).trans hR
    have hr : 0 < R - 1 := by linarith
    have hI := (cauchy_weight_integral hr).1.const_mul (B + ‖f 1‖)
    calc
      _ ≤ ∫ t : ℝ, (B + ‖f 1‖) * ((R-1)^2+t^2)⁻¹ :=
        norm_integral_le_of_norm_le hI (by
          filter_upwards [] with t
          simpa only [div_eq_mul_inv] using halfPlaneDifference_far_bound f B hR2 t (hB (line R t) (by simpa [line] using (le_max_right 2 R₀).trans hR)))
      _ = _ := by rw [integral_const_mul, (cauchy_weight_integral hr).2]
  have ht : Tendsto (fun R : ℝ => (B + ‖f 1‖) * (Real.pi / (R-1))) atTop (𝓝 0) := by
    have hi : Tendsto (fun R : ℝ => (R-1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
    simpa only [sub_eq_add_neg, div_eq_mul_inv, mul_zero] using (hi.const_mul Real.pi).const_mul (B + ‖f 1‖)
  have hc : Tendsto (fun _R : ℝ => ∫ t : ℝ, halfPlaneDifference f (line 0 t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_ge_atTop (max (2 : ℝ) R₀)] with R hR
    rw [halfPlaneDifference_integral_eq f hd hg (by have := (le_max_left 2 R₀).trans hR; linarith : 0 ≤ R)]
    exact hbound R hR
  exact tendsto_nhds_unique tendsto_const_nhds hc

lemma halfPlane_weighted_cauchy (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    (hb : ∃ R₀ B : ℝ, ∀ z : ℂ, R₀ ≤ z.re → ‖f z‖ ≤ B) :
    Integrable (fun t : ℝ => f (line 0 t) / (1 + (t : ℂ) ^ 2)) ∧
      (∫ t : ℝ, f (line 0 t) / (1 + (t : ℂ) ^ 2)) = (Real.pi : ℂ) * f 1 := by
  have hconst : Integrable (fun t : ℝ => f 1 * (((1 + t ^ 2)⁻¹ : ℝ) : ℂ)) :=
    integrable_inv_one_add_sq.ofReal.const_mul _
  have he (t : ℝ) : f (line 0 t) / (1 + (t : ℂ) ^ 2) =
      halfPlaneDifference f (line 0 t) + f 1 * (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [halfPlaneDifference_boundary]
    push_cast
    ring
  have hi := halfPlaneDifference_line_integrable f hd hg (x := 0) le_rfl
  refine ⟨(hi.add hconst).congr (Eventually.of_forall (fun t => (he t).symm)), ?_⟩
  simp_rw [he]
  rw [integral_add hi hconst, halfPlaneDifference_integral_zero f hd hg hb, zero_add,
    integral_const_mul, integral_complex_ofReal, integral_univ_inv_one_add_sq, mul_comm]

lemma complex_norm_sq_eq_twice_re_sq_sub_sq_re (z : ℂ) :
    ‖z‖ ^ 2 = 2 * z.re ^ 2 - (z ^ 2).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  ring

lemma halfPlane_weighted_realPart (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/4 : ℝ))
    (hb : ∃ R₀ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, R₀ ≤ z.re → ‖f z‖ ≤ B)
    (hI : Integrable (fun t : ℝ => ‖f (line 0 t)‖ ^ 2 / (1 + t ^ 2))) :
    Integrable (fun t : ℝ => (f (line 0 t)).re ^ 2 / (1 + t ^ 2)) ∧
      (∫ t : ℝ, ‖f (line 0 t)‖ ^ 2 / (1 + t ^ 2)) ≤
        2 * (∫ t : ℝ, (f (line 0 t)).re ^ 2 / (1 + t ^ 2)) + Real.pi * ‖f 1‖ ^ 2 := by
  have hsq := halfPlane_weighted_cauchy (fun z => f z ^ 2)
    (fun z hz => (hd z hz).pow 2) (by
      intro R hR
      obtain ⟨C,hC,hg⟩ := hg R hR
      refine ⟨C ^ 2, sq_nonneg _, ?_⟩
      intro x hx t
      rw [norm_pow]
      have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hg x hx t)
      have hp : ((1 + |t|) ^ (1/4 : ℝ)) ^ 2 = (1 + |t|) ^ (1/2 : ℝ) := by
        rw [← Real.rpow_natCast ((1 + |t|) ^ (1/4 : ℝ)) 2,
          ← Real.rpow_mul (by positivity : 0 ≤ 1 + |t|)]
        norm_num
      simpa only [mul_pow, hp] using hh) (by
      obtain ⟨R₀,B,hB,hb⟩ := hb
      refine ⟨R₀, B ^ 2, ?_⟩
      intro z hz
      rw [norm_pow]
      exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb z hz))
  have hir : Integrable (fun t : ℝ => (f (line 0 t)).re ^ 2 / (1 + t ^ 2)) := by
    apply hI.mono' ?_ (Eventually.of_forall (fun t => ?_))
    · apply Continuous.aestronglyMeasurable
      have hc : Continuous (fun t : ℝ => f (line 0 t)) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact (hd (line 0 t) (by simp [line])).continuousAt.comp
          (show ContinuousAt (fun t : ℝ => line 0 t) t by unfold line; fun_prop)
      exact ((Complex.continuous_re.comp hc).pow 2).div (by fun_prop) (by intro t; positivity)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := Complex.abs_re_le_norm (f (line 0 t))
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hh
  have he (t : ℝ) : ‖f (line 0 t)‖ ^ 2 / (1 + t ^ 2) =
      2 * ((f (line 0 t)).re ^ 2 / (1 + t ^ 2)) -
        (f (line 0 t) ^ 2 / (1 + (t : ℂ) ^ 2)).re := by
    rw [complex_norm_sq_eq_twice_re_sq_sub_sq_re]
    have hh : (f (line 0 t) ^ 2 / (1 + (t : ℂ) ^ 2)).re =
        (f (line 0 t) ^ 2).re / (1 + t ^ 2) := by
      rw [show (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.div_ofReal_re _ _
    rw [hh]
    ring
  refine ⟨hir, ?_⟩
  simp_rw [he]
  have hsqre : Integrable (fun t : ℝ => (f (line 0 t) ^ 2 / (1 + (t : ℂ) ^ 2)).re) := hsq.1.re
  have heint : (∫ t : ℝ, (f (line 0 t) ^ 2 / (1 + (t : ℂ) ^ 2)).re) =
      (∫ t : ℝ, f (line 0 t) ^ 2 / (1 + (t : ℂ) ^ 2)).re := integral_re hsq.1
  rw [integral_sub (hir.const_mul 2) hsqre, integral_const_mul, heint, hsq.2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hr : -(f 1 ^ 2).re ≤ ‖f 1‖ ^ 2 := by
    have hh := (neg_le_abs (f 1 ^ 2).re).trans (Complex.abs_re_le_norm (f 1 ^ 2))
    simpa only [norm_pow] using hh
  have hh := mul_le_mul_of_nonneg_left hr Real.pi_pos.le
  linarith

end ConditionalGoldbach
