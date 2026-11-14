module

public import ConditionalGoldbach.Proofs.SpectralPoissonConvolution
public import ConditionalGoldbach.Proofs.HardyContourShift

/-! Fourier inversion of the one-sided exponential supplies the smoothed Perron kernel. -/
@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology FourierTransform Convolution
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def perronExponential (c x : ℝ) : ℂ := if 0 < x then Complex.exp (-((c * x : ℝ) : ℂ)) else 0

lemma perronExponential_integrable {c : ℝ} (hc : 0 < c) : Integrable (perronExponential c) := by
  have he : perronExponential c = (Ioi (0 : ℝ)).indicator
      (fun x : ℝ => Complex.exp ((-(c : ℂ)) * x)) := by
    funext x
    by_cases hx : 0 < x <;> simp [perronExponential, Set.indicator, hx, ofReal_mul]
  rw [he, integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hc) 0

lemma perronExponential_fourier {c : ℝ} (hc : 0 < c) (t : ℝ) :
    𝓕 (perronExponential c) t = ((c : ℂ) + (2 * Real.pi * t : ℝ) * I)⁻¹ := by
  let z : ℂ := -(c : ℂ) - (2 * Real.pi * t : ℝ) * I
  have hz : z.re < 0 := by simpa [z] using neg_neg_of_pos hc
  have he : (fun u : ℝ => Complex.exp ((-2 * Real.pi * (t * u) : ℝ) * I) *
      perronExponential c u) = (Ioi (0 : ℝ)).indicator (fun u => Complex.exp (z * u)) := by
    funext u
    by_cases hu : 0 < u
    · simp only [perronExponential, hu, ite_true, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu), ← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring
    · simp [perronExponential, hu, Set.indicator]
  rw [Real.fourier_eq']
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul, he,
    integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi hz]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  dsimp [z]
  rw [show -(c : ℂ) - (2 * Real.pi * t : ℝ) * I = -((c : ℂ) + (2 * Real.pi * t : ℝ) * I) by ring,
    div_neg, neg_div, neg_neg, one_div]

lemma perronExponential_convolution (c x : ℝ) :
    (convolution (perronExponential c) (perronExponential c) (ContinuousLinearMap.mul ℂ ℂ)) x =
      ((max x 0 : ℝ) : ℂ) * Complex.exp (-((c * x : ℝ) : ℂ)) := by
  change (∫ u : ℝ, perronExponential c u * perronExponential c (x - u)) = _
  have he : (fun u : ℝ => perronExponential c u * perronExponential c (x - u)) =
      (Ioo (0 : ℝ) x).indicator (fun _ => Complex.exp (-((c * x : ℝ) : ℂ))) := by
    funext u
    by_cases hu : 0 < u
    · by_cases hx : u < x
      · have hxu : 0 < x - u := by linarith
        simp only [perronExponential, hu, hxu, ite_true, Set.indicator_of_mem (show u ∈ Ioo (0 : ℝ) x from ⟨hu, hx⟩), ← Complex.exp_add]
        congr 1
        push_cast
        ring
      · have hxu : ¬0 < x - u := by linarith
        simp [perronExponential, hu, hxu, Set.indicator, hx]
    · simp [perronExponential, hu, Set.indicator]
  rw [he, integral_indicator measurableSet_Ioo, setIntegral_const]
  simp only [Measure.real, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal',
    Complex.real_smul]

lemma perronCauchySquare_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (((c : ℂ) + (2 * Real.pi * t : ℝ) * I)⁻¹)^2) := by
  have hnorm (t : ℝ) : ‖(((c : ℂ) + (2 * Real.pi * t : ℝ) * I)⁻¹)^2‖ =
      c⁻¹^2 * (1 + ((2 * Real.pi / c) * t)^2)⁻¹ := by
    rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
    field_simp
  apply (integrable_norm_iff (by fun_prop)).mp
  simp_rw [hnorm]
  exact (integrable_inv_one_add_mul_sq (div_ne_zero (by positivity) hc.ne')).const_mul _

lemma perronCauchySquare_fourierInv {c : ℝ} (hc : 0 < c) (x : ℝ) :
    𝓕⁻ (fun t : ℝ => (((c : ℂ) + (2 * Real.pi * t : ℝ) * I)⁻¹)^2) x =
      ((max x 0 : ℝ) : ℂ) * Complex.exp (-((c * x : ℝ) : ℂ)) := by
  let f := convolution (perronExponential c) (perronExponential c) (ContinuousLinearMap.mul ℂ ℂ)
  have hfi : Integrable f := (perronExponential_integrable hc).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (perronExponential_integrable hc)
  have hF : 𝓕 f = fun t : ℝ => (((c : ℂ) + (2 * Real.pi * t : ℝ) * I)⁻¹)^2 := by
    funext t
    rw [Real.fourier_mul_convolution_eq (perronExponential_integrable hc) (perronExponential_integrable hc),
      perronExponential_fourier hc, pow_two]
  have hcF : Continuous f := by
    have he : f = fun x : ℝ => ((max x 0 : ℝ) : ℂ) * Complex.exp (-((c * x : ℝ) : ℂ)) :=
      funext (perronExponential_convolution c)
    rw [he]
    fun_prop
  have hh := congrFun (hcF.fourierInv_fourier_eq hfi (by rw [hF]; exact perronCauchySquare_integrable hc)) x
  rw [hF] at hh
  exact hh.trans (perronExponential_convolution c x)

lemma perron_positivePart_integrable {c Y : ℝ} (hc : 0 < c) (hY : 0 < Y) :
    Integrable (fun t : ℝ => (Y : ℂ)^(line c (2 * Real.pi * t)) /
      (line c (2 * Real.pi * t))^2) := by
  have hv (t : ℝ) : line c (2 * Real.pi * t) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp [line] at hh
    linarith
  apply (integrable_norm_iff (by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · apply Continuous.const_cpow (by unfold line; fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
    · unfold line
      fun_prop
    · intro t
      exact pow_ne_zero _ (hv t))).mp
  apply ((perronCauchySquare_integrable hc).norm.const_mul (Y^c)).congr
  filter_upwards [] with t
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    norm_pow, norm_inv, inv_pow, div_eq_mul_inv]

/-- Perron's second-order kernel is the positive logarithm, with the `2π` normalization
built into the vertical coordinate. -/
lemma perron_positivePart_integral {c Y : ℝ} (hc : 0 < c) (hY : 0 < Y) :
    (∫ t : ℝ, (Y : ℂ)^(line c (2 * Real.pi * t)) /
      (line c (2 * Real.pi * t))^2) = ((max (Real.log Y) 0 : ℝ) : ℂ) := by
  have hh := perronCauchySquare_fourierInv hc (Real.log Y)
  rw [Real.fourierInv_eq'] at hh
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul] at hh
  have he : (fun t : ℝ => (Y : ℂ)^(line c (2 * Real.pi * t)) /
      (line c (2 * Real.pi * t))^2) = fun t : ℝ =>
      Complex.exp ((c * Real.log Y : ℝ) : ℂ) *
        (Complex.exp ((2 * Real.pi * (t * Real.log Y) : ℝ) * I) *
          (((c : ℂ) + (2 * Real.pi * t : ℝ) * I)⁻¹)^2) := by
    funext t
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne'),
      ← Complex.ofReal_log hY.le]
    have hexp : (Real.log Y : ℂ) * line c (2 * Real.pi * t) =
        ((c * Real.log Y : ℝ) : ℂ) + (2 * Real.pi * (t * Real.log Y) : ℝ) * I := by
      unfold line
      push_cast
      ring
    rw [hexp, Complex.exp_add]
    simp only [line, div_eq_mul_inv, inv_pow]
    ring
  rw [he, integral_const_mul]
  have hh' : (∫ t : ℝ, Complex.exp ((2 * Real.pi * (t * Real.log Y) : ℝ) * I) *
      (((c : ℂ) + (2 * Real.pi * t : ℝ) * I)⁻¹)^2) =
      ((max (Real.log Y) 0 : ℝ) : ℂ) * Complex.exp (-((c * Real.log Y : ℝ) : ℂ)) := by
    convert hh using 1
    congr 1
    funext t
    congr 2
    push_cast
    ring
  rw [hh']
  calc
    _ = ((max (Real.log Y) 0 : ℝ) : ℂ) *
        (Complex.exp ((c * Real.log Y : ℝ) : ℂ) * Complex.exp (-((c * Real.log Y : ℝ) : ℂ))) := by ring
    _ = _ := by rw [← Complex.exp_add]; simp

lemma smoothedPerronWeight_positiveParts {X : ℝ} (hX : 1 < X) (n : ℕ) (hn : 0 < n) :
    smoothedPerronWeight X n =
      (max (Real.log (X / n)) 0 - max (Real.log (Real.sqrt X / n)) 0) /
        Real.log (Real.sqrt X) := by
  have hx : 0 < X := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
  have hls : 0 < Real.log (Real.sqrt X) := Real.log_pos hs
  have hsq : Real.log X = 2 * Real.log (Real.sqrt X) := by rw [Real.log_sqrt hx.le]; ring
  rw [Real.log_div hx.ne' hnR.ne', Real.log_div (by linarith : Real.sqrt X ≠ 0) hnR.ne']
  unfold smoothedPerronWeight
  split_ifs with hsmall hlarge
  · have hln : Real.log n ≤ Real.log (Real.sqrt X) := Real.log_le_log hnR hsmall
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    rw [hsq]
    field_simp; ring
  · have hln : Real.log (Real.sqrt X) < Real.log n := Real.log_lt_log (by linarith) (lt_of_not_ge hsmall)
    have hlnX : Real.log n ≤ Real.log X := Real.log_le_log hnR hlarge
    rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero,
      Real.log_div hx.ne' hnR.ne']
  · have hln : Real.log X < Real.log n := Real.log_lt_log hx (lt_of_not_ge hlarge)
    rw [max_eq_right (by linarith), max_eq_right (by linarith), sub_self, zero_div]

lemma perron_weight_integrand_eq {X : ℝ} (hX : 1 < X) (n : ℕ) (hn : 0 < n) (v : ℂ) :
    (n : ℂ)^(-v) * smoothedPerronKernel X v =
      (((X / (n : ℝ) : ℝ) : ℂ)^v / v^2 -
        ((Real.sqrt X / (n : ℝ) : ℝ) : ℂ)^v / v^2) / (Real.log (Real.sqrt X) : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Complex.ofReal_div]
  rw [Complex.div_cpow_ofReal_nonneg (by linarith) hnR.le,
    Complex.div_cpow_ofReal_nonneg (Real.sqrt_nonneg _) hnR.le]
  simp only [Complex.ofReal_natCast]
  unfold smoothedPerronKernel
  rw [Complex.cpow_neg]
  ring

lemma integral_div_const_complex (f : ℝ → ℂ) (z : ℂ) :
    (∫ t : ℝ, f t / z) = (∫ t : ℝ, f t) / z := by
  simp only [div_eq_mul_inv, integral_mul_const]

/-- The actual cutoff weight is the integral of the smoothed Perron kernel. -/
lemma perron_weight_integral {X c : ℝ} (hX : 1 < X) (hc : 0 < c) (n : ℕ) (hn : 0 < n) :
    Integrable (fun t : ℝ => (n : ℂ)^(-line c (2 * Real.pi * t)) *
      smoothedPerronKernel X (line c (2 * Real.pi * t))) ∧
    (∫ t : ℝ, (n : ℂ)^(-line c (2 * Real.pi * t)) *
      smoothedPerronKernel X (line c (2 * Real.pi * t))) = (smoothedPerronWeight X n : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi₁ := perron_positivePart_integrable hc (div_pos (show 0 < X by linarith) hnR)
  have hi₂ := perron_positivePart_integrable hc (div_pos (Real.sqrt_pos.mpr (show 0 < X by linarith)) hnR)
  simp_rw [perron_weight_integrand_eq hX n hn]
  refine ⟨(hi₁.sub hi₂).div_const _, ?_⟩
  rw [integral_div_const_complex, integral_sub hi₁ hi₂,
    perron_positivePart_integral hc (div_pos (show 0 < X by linarith) hnR),
    perron_positivePart_integral hc (div_pos (Real.sqrt_pos.mpr (show 0 < X by linarith)) hnR),
    smoothedPerronWeight_positiveParts hX n hn]
  push_cast
  rfl

end ConditionalGoldbach
