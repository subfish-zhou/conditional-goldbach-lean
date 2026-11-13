import ConditionalGoldbach.Proofs.SpectralPerronPoleIntegral
import ConditionalGoldbach.Proofs.SpectralZeroPower
import ConditionalGoldbach.Proofs.HardyKernelMajorant

/-! Absolute integral majorants for exchanging the Hadamard zero sum with Perron integration. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma reciprocal_convolution_majorant (t δ : ℝ) :
    (1 + |t|)⁻¹ * (1 + |t + δ|)⁻¹ ≤
      (1 + |δ|)^(-(1 / 4 : ℝ)) / 2 *
        ((1 + |t|)^(-(3 / 2 : ℝ)) + (1 + |t + δ|)^(-(3 / 2 : ℝ))) := by
  let A := 1 + |t|
  let B := 1 + |t + δ|
  let D := 1 + |δ|
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hmul : D ≤ A * B := by
    have hh := abs_sub (t + δ) t
    rw [add_sub_cancel_left] at hh
    dsimp [A, B, D]
    nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (t + δ))]
  have hquarter : (A * B)^(-(1 / 4 : ℝ)) ≤ D^(-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg (mul_pos hA hB).le, Real.rpow_neg hD.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hD _) (Real.rpow_le_rpow hD.le hmul (by norm_num))
  have hprod : A⁻¹ * B⁻¹ = (A * B)^(-(1 / 4 : ℝ)) *
      (A^(-(3 / 4 : ℝ)) * B^(-(3 / 4 : ℝ))) := by
    rw [← Real.mul_rpow hA.le hB.le, ← Real.rpow_add (mul_pos hA hB)]
    norm_num [Real.rpow_neg_one, mul_inv]
    ring
  have hsqA : (A^(-(3 / 4 : ℝ)))^2 = A^(-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    norm_num
  have hsqB : (B^(-(3 / 4 : ℝ)))^2 = B^(-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    norm_num
  have ham : A^(-(3 / 4 : ℝ)) * B^(-(3 / 4 : ℝ)) ≤
      (A^(-(3 / 2 : ℝ)) + B^(-(3 / 2 : ℝ))) / 2 := by
    have hh := sq_nonneg (A^(-(3 / 4 : ℝ)) - B^(-(3 / 4 : ℝ)))
    rw [sub_sq, hsqA, hsqB] at hh
    linarith
  change A⁻¹ * B⁻¹ ≤ D^(-(1 / 4 : ℝ)) / 2 * (A^(-(3 / 2 : ℝ)) + B^(-(3 / 2 : ℝ)))
  rw [hprod]
  calc
    _ ≤ D^(-(1 / 4 : ℝ)) * (A^(-(3 / 4 : ℝ)) * B^(-(3 / 4 : ℝ))) := by gcongr
    _ ≤ D^(-(1 / 4 : ℝ)) * ((A^(-(3 / 2 : ℝ)) + B^(-(3 / 2 : ℝ))) / 2) := by gcongr
    _ = _ := by ring

lemma reciprocal_convolution_integrable_bound (δ : ℝ) :
    Integrable (fun t : ℝ => (1 + |t|)⁻¹ * (1 + |t + δ|)⁻¹) ∧
      (∫ t : ℝ, (1 + |t|)⁻¹ * (1 + |t + δ|)⁻¹) ≤
        (1 + |δ|)^(-(1 / 4 : ℝ)) * (∫ t : ℝ, (1 + |t|)^(-(3 / 2 : ℝ))) := by
  have hM := (hardy_decay_integrable.add (hardy_decay_integrable.comp_add_right δ)).const_mul
    ((1 + |δ|)^(-(1 / 4 : ℝ)) / 2)
  have hf : Integrable (fun t : ℝ => (1 + |t|)⁻¹ * (1 + |t + δ|)⁻¹) := by
    apply hM.mono' (by fun_prop)
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact reciprocal_convolution_majorant t δ
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ t : ℝ, (1 + |δ|)^(-(1 / 4 : ℝ)) / 2 *
        ((1 + |t|)^(-(3 / 2 : ℝ)) + (1 + |t + δ|)^(-(3 / 2 : ℝ))) :=
      integral_mono hf hM (reciprocal_convolution_majorant · δ)
    _ = _ := by
      rw [integral_const_mul, integral_add hardy_decay_integrable (hardy_decay_integrable.comp_add_right δ),
        integral_add_right_eq_self (fun t : ℝ => (1 + |t|)^(-(3 / 2 : ℝ))) δ]
      ring

lemma perron_line_inverse_bound {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(line c (2 * Real.pi * t))⁻¹‖ ≤
      (c⁻¹ + (2 * Real.pi)⁻¹) * (1 + |t|)⁻¹ := by
  have hr : c ≤ ‖line c (2 * Real.pi * t)‖ := by
    have hh := Complex.re_le_norm (line c (2 * Real.pi * t))
    simpa [line] using hh
  have hi : 2 * Real.pi * |t| ≤ ‖line c (2 * Real.pi * t)‖ := by
    have hh := Complex.abs_im_le_norm (line c (2 * Real.pi * t))
    simpa [line, abs_mul, abs_of_pos Real.pi_pos] using hh
  have hn : 0 < ‖line c (2 * Real.pi * t)‖ := hc.trans_le hr
  have hbound : 1 + |t| ≤ (c⁻¹ + (2 * Real.pi)⁻¹) * ‖line c (2 * Real.pi * t)‖ := by
    have hr' := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hc.le)
    have hi' := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (show 0 ≤ 2 * Real.pi by positivity))
    rw [inv_mul_cancel₀ hc.ne'] at hr'
    rw [← mul_assoc, inv_mul_cancel₀ (show 2 * Real.pi ≠ 0 by positivity), one_mul] at hi'
    nlinarith
  rw [norm_inv, inv_eq_one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ hn (by positivity)).mpr (by simpa using hbound)

def perronKernelNormConstant (X c : ℝ) : ℝ :=
  (X^c + (Real.sqrt X)^c) / Real.log (Real.sqrt X)

lemma perronKernelNormConstant_pos {X : ℝ} (hX : 1 < X) (c : ℝ) :
    0 < perronKernelNormConstant X c := by
  have hx : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
  exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _))
    (Real.log_pos hx)

lemma smoothedPerronKernel_norm_bound {X : ℝ} (hX : 1 < X) (c t : ℝ) :
    ‖smoothedPerronKernel X (line c (2 * Real.pi * t))‖ ≤
      perronKernelNormConstant X c * ‖(line c (2 * Real.pi * t))⁻¹‖^2 := by
  have hx : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
  unfold smoothedPerronKernel
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos hx)]
  calc
    _ ≤ (X^c + (Real.sqrt X)^c) / (‖line c (2 * Real.pi * t)‖^2 * Real.log (Real.sqrt X)) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (Real.log_pos hx).le)
      apply (norm_sub_le _ _).trans_eq
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < X by linarith),
        Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < Real.sqrt X by linarith)]
      simp [line]
    _ = _ := by simp only [perronKernelNormConstant, norm_inv, inv_pow, div_eq_mul_inv, mul_inv]; ring

lemma perron_resolvent_difference_norm_bound {X c σ : ℝ} (hX : 1 < X) (hc : 0 < c)
    (hσ : 0 < σ) (t δ : ℝ) :
    ‖smoothedPerronKernel X (line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t) + line σ (2 * Real.pi * δ))⁻¹ -
        (line σ (2 * Real.pi * δ))⁻¹)‖ ≤
      (perronKernelNormConstant X c * (c⁻¹ + (2 * Real.pi)⁻¹) *
        (σ⁻¹ + (2 * Real.pi)⁻¹) * ((c + σ)⁻¹ + (2 * Real.pi)⁻¹)) *
        (1 + |δ|)⁻¹ * ((1 + |t|)⁻¹ * (1 + |t + δ|)⁻¹) := by
  let v := line c (2 * Real.pi * t)
  let a := line σ (2 * Real.pi * δ)
  have hv : v ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp [v, line] at hh
    linarith
  have ha : a ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp [a, line] at hh
    linarith
  have hw : v + a ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp [v, a, line] at hh
    linarith
  have hwa : v + a = line (c + σ) (2 * Real.pi * (t + δ)) := by
    dsimp [v, a, line]
    push_cast
    ring
  have hbase : ‖smoothedPerronKernel X v * ((v + a)⁻¹ - a⁻¹)‖ ≤
      perronKernelNormConstant X c * ‖v⁻¹‖ * ‖a⁻¹‖ * ‖(v + a)⁻¹‖ := by
    rw [norm_mul, inv_sub_inv' hw ha, show a - (v + a) = -v by ring,
      norm_mul, norm_mul, norm_neg]
    have hk : ‖smoothedPerronKernel X v‖ ≤ perronKernelNormConstant X c * ‖v⁻¹‖^2 :=
      smoothedPerronKernel_norm_bound hX c t
    apply (mul_le_mul_of_nonneg_right hk
      (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))).trans_eq
    rw [norm_inv, norm_inv, norm_inv]
    field_simp [norm_ne_zero_iff.mpr hv]
    <;> ring
  apply hbase.trans
  have hB := (perronKernelNormConstant_pos hX c).le
  have h₁ := perron_line_inverse_bound hc t
  have h₂ := perron_line_inverse_bound hσ δ
  have h₃ := perron_line_inverse_bound (add_pos hc hσ) (t + δ)
  rw [← hwa] at h₃
  calc
    _ ≤ perronKernelNormConstant X c *
        ((c⁻¹ + (2 * Real.pi)⁻¹) * (1 + |t|)⁻¹) *
        ((σ⁻¹ + (2 * Real.pi)⁻¹) * (1 + |δ|)⁻¹) *
        (((c + σ)⁻¹ + (2 * Real.pi)⁻¹) * (1 + |t + δ|)⁻¹) := by
      gcongr
      all_goals positivity
    _ = _ := by ring

lemma smoothedPerronKernel_integral {X c : ℝ} (hX : 1 < X) (hc : 0 < c) :
    Integrable (fun t : ℝ => smoothedPerronKernel X (line c (2 * Real.pi * t))) ∧
      (∫ t : ℝ, smoothedPerronKernel X (line c (2 * Real.pi * t))) = 1 := by
  have hh := perron_weight_integral hX hc 1 (by norm_num)
  simpa [smoothedPerronWeight, show (1 : ℝ) ≤ Real.sqrt X from
    ((Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)).le] using hh

lemma perron_resolvent_difference_integral {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun t : ℝ => smoothedPerronKernel X (line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t) + a)⁻¹ - a⁻¹)) ∧
    (∫ t : ℝ, smoothedPerronKernel X (line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t) + a)⁻¹ - a⁻¹)) = smoothedPerronKernel X (-a) := by
  have h₁ := smoothedPerron_single_pole_integral hX hc ha
  have h₂ := smoothedPerronKernel_integral hX hc
  simp_rw [mul_sub, ← div_eq_mul_inv]
  refine ⟨h₁.1.sub (h₂.1.div_const a), ?_⟩
  rw [integral_sub h₁.1 (h₂.1.div_const a), integral_div_const_complex, h₁.2, h₂.2]
  simp

def perronResolventNormConstant (X c σ : ℝ) : ℝ :=
  perronKernelNormConstant X c * (c⁻¹ + (2 * Real.pi)⁻¹) *
    (σ⁻¹ + (2 * Real.pi)⁻¹) * ((c + σ)⁻¹ + (2 * Real.pi)⁻¹) *
      (∫ t : ℝ, (1 + |t|)^(-(3 / 2 : ℝ)))

lemma perron_resolvent_difference_integral_norm_bound {X c σ : ℝ}
    (hX : 1 < X) (hc : 0 < c) (hσ : 0 < σ) (δ : ℝ) :
    (∫ t : ℝ, ‖smoothedPerronKernel X (line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t) + line σ (2 * Real.pi * δ))⁻¹ -
        (line σ (2 * Real.pi * δ))⁻¹)‖) ≤
      perronResolventNormConstant X c σ * (1 + |δ|)^(-(5 / 4 : ℝ)) := by
  have hint := (perron_resolvent_difference_integral hX hc
    (show 0 < (line σ (2 * Real.pi * δ)).re by simpa [line] using hσ)).1.norm
  have hconv := reciprocal_convolution_integrable_bound δ
  let B := perronKernelNormConstant X c * (c⁻¹ + (2 * Real.pi)⁻¹) *
    (σ⁻¹ + (2 * Real.pi)⁻¹) * ((c + σ)⁻¹ + (2 * Real.pi)⁻¹)
  have hB : 0 ≤ B := by
    have hh := (perronKernelNormConstant_pos hX c).le
    dsimp [B]
    positivity
  have hM := hconv.1.const_mul (B * (1 + |δ|)⁻¹)
  calc
    _ ≤ ∫ t : ℝ, B * (1 + |δ|)⁻¹ * ((1 + |t|)⁻¹ * (1 + |t + δ|)⁻¹) :=
      integral_mono hint hM (perron_resolvent_difference_norm_bound hX hc hσ · δ)
    _ = B * (1 + |δ|)⁻¹ * (∫ t : ℝ, (1 + |t|)⁻¹ * (1 + |t + δ|)⁻¹) := integral_const_mul _ _
    _ ≤ B * (1 + |δ|)⁻¹ * ((1 + |δ|)^(-(1 / 4 : ℝ)) *
        (∫ t : ℝ, (1 + |t|)^(-(3 / 2 : ℝ)))) := by gcongr; exact hconv.2
    _ = _ := by
      rw [show (1 + |δ|)⁻¹ = (1 + |δ|)^(-1 : ℝ) by rw [Real.rpow_neg_one]]
      have he : (1 + |δ|)^(-1 : ℝ) * (1 + |δ|)^(-(1 / 4 : ℝ)) =
          (1 + |δ|)^(-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_add (by positivity)]
        norm_num
      dsimp [perronResolventNormConstant, B]
      calc
        _ = perronKernelNormConstant X c * (c⁻¹ + (2 * Real.pi)⁻¹) *
          (σ⁻¹ + (2 * Real.pi)⁻¹) * ((c + σ)⁻¹ + (2 * Real.pi)⁻¹) *
          (∫ t : ℝ, (1 + |t|)^(-(3 / 2 : ℝ))) *
          ((1 + |δ|)^(-1 : ℝ) * (1 + |δ|)^(-(1 / 4 : ℝ))) := by ring
        _ = _ := by rw [he]

lemma integrable_tsum_of_summable_norm_integral {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℂ} (hF : ∀ i, Integrable (F i))
    (hsum : Summable (fun i => ∫ t : ℝ, ‖F i t‖)) :
    Integrable (fun t : ℝ => ∑' i, F i t) := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hF i).1), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun i => (hF i).1.enorm)]
  have he (i : ι) : (∫⁻ t : ℝ, ‖F i t‖ₑ) = ‖∫ t : ℝ, ‖F i t‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F i t)))]
    simp only [coe_nnnorm]
  simp_rw [he]
  exact lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mpr
    (NNReal.summable_coe.mp hsum.abs))

lemma perron_resolvent_sum_integral {ι : Type*} [Countable ι]
    {X c σ : ℝ} (hX : 1 < X) (hc : 0 < c) (hσ : 0 < σ)
    (δ : ι → ℝ) (hδ : Summable (fun i => (1 + |δ i|)^(-(5 / 4 : ℝ)))) :
    Integrable (fun t : ℝ => ∑' i, smoothedPerronKernel X (line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t) + line σ (2 * Real.pi * δ i))⁻¹ -
        (line σ (2 * Real.pi * δ i))⁻¹)) ∧
    (∫ t : ℝ, ∑' i, smoothedPerronKernel X (line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t) + line σ (2 * Real.pi * δ i))⁻¹ -
        (line σ (2 * Real.pi * δ i))⁻¹)) =
      ∑' i, smoothedPerronKernel X (-line σ (2 * Real.pi * δ i)) := by
  let F := fun i t => smoothedPerronKernel X (line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t) + line σ (2 * Real.pi * δ i))⁻¹ -
        (line σ (2 * Real.pi * δ i))⁻¹)
  have hF (i : ι) : Integrable (F i) :=
    (perron_resolvent_difference_integral hX hc
      (show 0 < (line σ (2 * Real.pi * δ i)).re by simpa [line] using hσ)).1
  have hsum : Summable (fun i => ∫ t : ℝ, ‖F i t‖) :=
    (hδ.mul_left (perronResolventNormConstant X c σ)).of_nonneg_of_le
      (fun i => integral_nonneg (fun t => norm_nonneg _))
      (fun i => perron_resolvent_difference_integral_norm_bound hX hc hσ (δ i))
  refine ⟨integrable_tsum_of_summable_norm_integral hF hsum, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hF hsum]
  apply tsum_congr
  intro i
  exact (perron_resolvent_difference_integral hX hc
    (show 0 < (line σ (2 * Real.pi * δ i)).re by simpa [line] using hσ)).2

end ConditionalGoldbach
