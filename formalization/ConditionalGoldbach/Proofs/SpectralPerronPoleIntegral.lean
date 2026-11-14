module

public import ConditionalGoldbach.Proofs.SpectralPerronIntegral

/-! The one-pole Perron transform, evaluated by Fourier inversion of exponential differences. -/
@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology FourierTransform
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def perronComplexExponential (a : ℂ) (x : ℝ) : ℂ := if 0 < x then Complex.exp (-a * x) else 0

lemma perronComplexExponential_integrable {a : ℂ} (ha : 0 < a.re) :
    Integrable (perronComplexExponential a) := by
  have he : perronComplexExponential a = (Ioi (0 : ℝ)).indicator
      (fun x : ℝ => Complex.exp (-a * x)) := by
    funext x
    by_cases hx : 0 < x <;> simp [perronComplexExponential, Set.indicator, hx]
  rw [he, integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos ha) 0

lemma perronComplexExponential_fourier {a : ℂ} (ha : 0 < a.re) (t : ℝ) :
    𝓕 (perronComplexExponential a) t = (a + (2 * Real.pi * t : ℝ) * I)⁻¹ := by
  let z : ℂ := -a - (2 * Real.pi * t : ℝ) * I
  have hz : z.re < 0 := by simpa [z] using neg_neg_of_pos ha
  have he : (fun u : ℝ => Complex.exp ((-2 * Real.pi * (t * u) : ℝ) * I) *
      perronComplexExponential a u) = (Ioi (0 : ℝ)).indicator (fun u => Complex.exp (z * u)) := by
    funext u
    by_cases hu : 0 < u
    · simp only [perronComplexExponential, hu, ite_true,
        Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu), ← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring
    · simp [perronComplexExponential, hu, Set.indicator]
  rw [Real.fourier_eq']
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul, he,
    integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi hz]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  dsimp [z]
  rw [show -a - (2 * Real.pi * t : ℝ) * I = -(a + (2 * Real.pi * t : ℝ) * I) by ring,
    div_neg, neg_div, neg_neg, one_div]

lemma complexFourier_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (fun x => f x - g x) = fun t => 𝓕 f t - 𝓕 g t := by
  have hi (k : ℝ → ℂ) (hk : Integrable k) (t : ℝ) :
      Integrable (fun u => Complex.exp ((-2 * Real.pi * (t * u) : ℝ) * I) * k u) := by
    apply hk.norm.mono' ((show Continuous (fun u : ℝ =>
      Complex.exp ((-2 * Real.pi * (t * u) : ℝ) * I)) by fun_prop).aestronglyMeasurable.mul hk.aestronglyMeasurable)
    filter_upwards [] with u
    simp [Complex.norm_exp]
  funext t
  simp only [Real.fourier_eq', RCLike.inner_apply, conj_trivial, smul_eq_mul, mul_sub]
  rw [integral_sub (hi f hf t) (hi g hg t)]

lemma perronComplexCauchySquare_integrable {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun t : ℝ => ((a + (2 * Real.pi * t : ℝ) * I)⁻¹)^2) := by
  have hh := (perronCauchySquare_integrable ha).comp_add_right (a.im / (2 * Real.pi))
  apply hh.congr
  filter_upwards [] with t
  have he : (a.re : ℂ) + ((2 * Real.pi * (t + a.im / (2 * Real.pi)) : ℝ) : ℂ) * I =
      a + ((2 * Real.pi * t : ℝ) : ℂ) * I := by
    have heR : 2 * Real.pi * (t + a.im / (2 * Real.pi)) = 2 * Real.pi * t + a.im := by
      field_simp [Real.pi_ne_zero]
    rw [heR]
    apply Complex.ext <;> simp; ring
  rw [he]

lemma perronCauchyDifference_integrable {c : ℝ} (hc : 0 < c) {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun t : ℝ => (line c (2 * Real.pi * t))⁻¹ -
      (line c (2 * Real.pi * t) + a)⁻¹) := by
  let v := fun t => line c (2 * Real.pi * t)
  have hv (t : ℝ) : v t ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp [v, line] at hh
    linarith
  have hw (t : ℝ) : v t + a ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp [v, line] at hh
    linarith
  have h₁ : Integrable (fun t : ℝ => ‖(v t)⁻¹‖^2) := by
    simpa only [norm_pow, v, line] using (perronCauchySquare_integrable hc).norm
  have h₂ : Integrable (fun t : ℝ => ‖(v t + a)⁻¹‖^2) := by
    have hh := (perronComplexCauchySquare_integrable (a := (c : ℂ) + a) (by simp; linarith)).norm
    convert hh using 1
    funext t
    rw [norm_pow]
    congr 2
    dsimp [v, line]
    ring
  apply ((h₁.add h₂).const_mul (‖a‖ / 2)).mono'
    (show Continuous (fun t : ℝ => (v t)⁻¹ - (v t + a)⁻¹) from
      ((by unfold v line; fun_prop : Continuous v).inv₀ hv).sub
        (((by unfold v line; fun_prop : Continuous v).add continuous_const).inv₀ hw)).aestronglyMeasurable
  filter_upwards [] with t
  rw [inv_sub_inv' (hv t) (hw t), add_sub_cancel_left, norm_mul, norm_mul]
  dsimp only [Pi.add_apply]
  have hh := mul_nonneg (norm_nonneg a) (sq_nonneg (‖(v t)⁻¹‖ - ‖(v t + a)⁻¹‖))
  nlinarith

lemma perronCauchyDifference_fourierInv {c : ℝ} (hc : 0 < c) {a : ℂ} (ha : 0 < a.re)
    (x : ℝ) (hx : 0 < x) :
    𝓕⁻ (fun t : ℝ => (line c (2 * Real.pi * t))⁻¹ -
      (line c (2 * Real.pi * t) + a)⁻¹) x =
      Complex.exp (-(c : ℂ) * x) * (1 - Complex.exp (-a * x)) := by
  let f : ℝ → ℂ := fun y => perronComplexExponential (c : ℂ) y - perronComplexExponential ((c : ℂ) + a) y
  have hca : 0 < ((c : ℂ) + a).re := by simp; linarith
  have hf : Integrable f := (perronComplexExponential_integrable hc).sub (perronComplexExponential_integrable hca)
  have hF : 𝓕 f = fun t : ℝ => (line c (2 * Real.pi * t))⁻¹ -
      (line c (2 * Real.pi * t) + a)⁻¹ := by
    rw [complexFourier_sub (perronComplexExponential_integrable hc) (perronComplexExponential_integrable hca)]
    funext t
    rw [perronComplexExponential_fourier hc, perronComplexExponential_fourier hca]
    dsimp [line]
    congr 2
    ring
  have hfc : Continuous f := by
    have he : f = fun y : ℝ => Complex.exp (-(c : ℂ) * (max y 0 : ℝ)) -
        Complex.exp (-((c : ℂ) + a) * (max y 0 : ℝ)) := by
      funext y
      by_cases hy : 0 < y
      · simp [f, perronComplexExponential, hy, max_eq_left hy.le]
      · simp [f, perronComplexExponential, hy, max_eq_right (le_of_not_gt hy)]
    rw [he]
    fun_prop
  have hh := congrFun (hfc.fourierInv_fourier_eq hf (by rw [hF]; exact perronCauchyDifference_integrable hc ha)) x
  rw [hF] at hh
  rw [hh]
  dsimp [f, perronComplexExponential]
  rw [ite_eq_left hx, ite_eq_left hx, mul_sub, mul_one, ← Complex.exp_add]
  congr 1
  congr 1
  ring

lemma perron_phase_mul_integrable {Y : ℝ} (hY : 0 < Y) (c : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ => (Y : ℂ)^(line c (2 * Real.pi * t)) * f t) := by
  have hc : Continuous (fun t : ℝ => (Y : ℂ)^(line c (2 * Real.pi * t))) :=
    Continuous.const_cpow (by unfold line; fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  apply (hf.norm.const_mul (Y^c)).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with t
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp [line]

lemma perron_phase_integral {Y : ℝ} (hY : 0 < Y) (c : ℝ) (f : ℝ → ℂ) :
    (∫ t : ℝ, (Y : ℂ)^(line c (2 * Real.pi * t)) * f t) =
      Complex.exp ((c * Real.log Y : ℝ) : ℂ) * 𝓕⁻ f (Real.log Y) := by
  have he (t : ℝ) : (Y : ℂ)^(line c (2 * Real.pi * t)) =
      Complex.exp ((c * Real.log Y : ℝ) : ℂ) *
        Complex.exp ((2 * Real.pi * (t * Real.log Y) : ℝ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne'),
      ← Complex.ofReal_log hY.le, ← Complex.exp_add]
    congr 1
    unfold line
    push_cast
    ring
  simp_rw [he, mul_assoc]
  rw [integral_const_mul, Real.fourierInv_eq']
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  congr 2
  funext t
  congr 2
  push_cast
  ring

lemma perronCauchyDifference_integral {c Y : ℝ} (hc : 0 < c) (hY : 1 < Y)
    {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ, (Y : ℂ)^(line c (2 * Real.pi * t)) *
      ((line c (2 * Real.pi * t))⁻¹ - (line c (2 * Real.pi * t) + a)⁻¹)) =
      1 - (Y : ℂ)^(-a) := by
  rw [perron_phase_integral (show 0 < Y by linarith),
    perronCauchyDifference_fourierInv hc ha _ (Real.log_pos hY)]
  rw [show -(c : ℂ) * (Real.log Y : ℂ) = -((c * Real.log Y : ℝ) : ℂ) by push_cast; ring,
    ← mul_assoc, ← Complex.exp_add]
  simp only [add_neg_cancel, Complex.exp_zero, one_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (show Y ≠ 0 by linarith)),
    ← Complex.ofReal_log (show 0 ≤ Y by linarith)]
  congr 2
  ring

lemma perron_single_pole_integral {c Y : ℝ} (hc : 0 < c) (hY : 1 < Y)
    {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun t : ℝ => (Y : ℂ)^(line c (2 * Real.pi * t)) /
      ((line c (2 * Real.pi * t))^2 * (line c (2 * Real.pi * t) + a))) ∧
    (∫ t : ℝ, (Y : ℂ)^(line c (2 * Real.pi * t)) /
      ((line c (2 * Real.pi * t))^2 * (line c (2 * Real.pi * t) + a))) =
      (Real.log Y : ℂ) / a - (1 - (Y : ℂ)^(-a)) / a^2 := by
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  have hi₁ := (perron_positivePart_integrable hc (show 0 < Y by linarith)).div_const a
  have hi₂ := (perron_phase_mul_integrable (show 0 < Y by linarith) c
    (perronCauchyDifference_integrable hc ha)).div_const (a^2)
  have he (t : ℝ) : (Y : ℂ)^(line c (2 * Real.pi * t)) /
      ((line c (2 * Real.pi * t))^2 * (line c (2 * Real.pi * t) + a)) =
      ((Y : ℂ)^(line c (2 * Real.pi * t)) / (line c (2 * Real.pi * t))^2) / a -
      ((Y : ℂ)^(line c (2 * Real.pi * t)) *
        ((line c (2 * Real.pi * t))⁻¹ - (line c (2 * Real.pi * t) + a)⁻¹)) / a^2 := by
    have hv : line c (2 * Real.pi * t) ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp [line] at hh
      linarith
    have hw : line c (2 * Real.pi * t) + a ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp [line] at hh
      linarith
    field_simp
    ring
  simp_rw [he]
  refine ⟨hi₁.sub hi₂, ?_⟩
  rw [integral_sub hi₁ hi₂, integral_div_const_complex, integral_div_const_complex,
    perron_positivePart_integral hc (show 0 < Y by linarith),
    max_eq_left (Real.log_pos hY).le, perronCauchyDifference_integral hc hY ha]

/-- A nontrivial zero contributes precisely the paper's smoothed Perron residue. -/
lemma smoothedPerron_single_pole_integral {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun t : ℝ => smoothedPerronKernel X (line c (2 * Real.pi * t)) /
      (line c (2 * Real.pi * t) + a)) ∧
    (∫ t : ℝ, smoothedPerronKernel X (line c (2 * Real.pi * t)) /
      (line c (2 * Real.pi * t) + a)) = a⁻¹ + smoothedPerronKernel X (-a) := by
  have hx : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  have hl0 : (Real.log (Real.sqrt X) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hx).ne'
  have h₁ := perron_single_pole_integral hc hX ha
  have h₂ := perron_single_pole_integral hc hx ha
  have he (t : ℝ) : smoothedPerronKernel X (line c (2 * Real.pi * t)) /
      (line c (2 * Real.pi * t) + a) =
      ((X : ℂ)^(line c (2 * Real.pi * t)) /
        ((line c (2 * Real.pi * t))^2 * (line c (2 * Real.pi * t) + a)) -
       (Real.sqrt X : ℂ)^(line c (2 * Real.pi * t)) /
        ((line c (2 * Real.pi * t))^2 * (line c (2 * Real.pi * t) + a))) /
          (Real.log (Real.sqrt X) : ℂ) := by
    unfold smoothedPerronKernel
    simp only [div_eq_mul_inv, mul_inv]
    ring
  simp_rw [he]
  refine ⟨(h₁.1.sub h₂.1).div_const _, ?_⟩
  rw [integral_div_const_complex, integral_sub h₁.1 h₂.1, h₁.2, h₂.2]
  have hlog : (Real.log X : ℂ) = 2 * (Real.log (Real.sqrt X) : ℂ) := by
    rw [Real.log_sqrt (by linarith : 0 ≤ X)]
    push_cast
    ring
  rw [hlog, smoothedPerronKernel]
  field_simp
  ring

end ConditionalGoldbach
