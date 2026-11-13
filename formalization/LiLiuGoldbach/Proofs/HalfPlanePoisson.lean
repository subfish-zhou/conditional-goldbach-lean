import LiLiuGoldbach.Proofs.HalfPlaneWeightedCauchy
import LiLiuGoldbach.Proofs.SpectralPoissonConvolution

/-! Poisson representation and the square majorant on a right half-plane. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16

lemma halfPlane_affine_cauchy (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    (hb : ∃ R₀ B : ℝ, ∀ z : ℂ, R₀ ≤ z.re → ‖f z‖ ≤ B)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    Integrable (fun v : ℝ => f (line 0 (ℓ*v+t)) / (1 + (v : ℂ)^2)) ∧
      (∫ v : ℝ, f (line 0 (ℓ*v+t)) / (1 + (v : ℂ)^2)) = (Real.pi : ℂ) * f (line ℓ t) := by
  let F : ℂ → ℂ := fun z => f ((ℓ : ℂ)*z+(t : ℂ)*I)
  have he (x v : ℝ) : (ℓ : ℂ)*line x v+(t : ℂ)*I = line (ℓ*x) (ℓ*v+t) := by
    unfold line; push_cast; ring
  have hF := halfPlane_weighted_cauchy F (by
    intro z hz
    apply (hd ((ℓ : ℂ)*z+(t : ℂ)*I) (by simpa using mul_nonneg hℓ.le hz)).comp z
    exact (differentiableAt_id.const_mul (ℓ : ℂ)).add_const ((t : ℂ)*I)) (by
    intro R hR
    obtain ⟨C,hC,hg⟩ := hg (ℓ*R) (mul_nonneg hℓ.le hR)
    refine ⟨C * (1+ℓ+|t|) ^ (1/2 : ℝ), by positivity, ?_⟩
    intro x hx v
    dsimp [F]
    rw [he]
    apply (hg (ℓ*x) ⟨mul_nonneg hℓ.le hx.1, mul_le_mul_of_nonneg_left hx.2 hℓ.le⟩ _).trans
    have hv : 1+|ℓ*v+t| ≤ (1+ℓ+|t|)*(1+|v|) := by
      have hh := abs_add_le (ℓ*v) t
      rw [abs_mul, abs_of_pos hℓ] at hh
      nlinarith [abs_nonneg v, abs_nonneg t, mul_nonneg (abs_nonneg t) (abs_nonneg v)]
    have hp := Real.rpow_le_rpow (by positivity) hv (by norm_num : (0 : ℝ) ≤ 1/2)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hp
    convert mul_le_mul_of_nonneg_left hp hC using 1 <;> ring) (by
    obtain ⟨R₀,B,hb⟩ := hb
    refine ⟨R₀/ℓ, B, ?_⟩
    intro z hz
    apply hb
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, sub_self, add_zero]
    simpa only [mul_comm] using (div_le_iff₀ hℓ).mp hz)
  have hz : (ℓ : ℂ)*1+(t : ℂ)*I = line ℓ t := by simp [line]
  simpa only [F, he, mul_zero, hz] using hF

lemma halfPlane_poisson (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    (hb : ∃ R₀ B : ℝ, ∀ z : ℂ, R₀ ≤ z.re → ‖f z‖ ≤ B)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    Integrable (fun v : ℝ => (poissonKernelReal ℓ (t-v) : ℂ) * f (line 0 v)) ∧
      (∫ v : ℝ, (poissonKernelReal ℓ (t-v) : ℂ) * f (line 0 v)) = f (line ℓ t) := by
  obtain ⟨hI,hE⟩ := halfPlane_affine_cauchy f hd hg hb hℓ t
  let g (v : ℝ) := f (line 0 (ℓ*v+t)) / (1 + (v : ℂ)^2)
  let k (v : ℝ) := (poissonKernelReal ℓ (t-v) : ℂ) * f (line 0 v)
  have he (v : ℝ) : k (ℓ*v+t) = ((Real.pi * ℓ : ℝ) : ℂ)⁻¹ * g v := by
    dsimp [k,g,poissonKernelReal]
    push_cast
    have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hv : 1+(v : ℂ)^2 ≠ 0 := by exact_mod_cast (by positivity : (1 : ℝ)+v^2 ≠ 0)
    have hd : (ℓ : ℂ)^2+((t : ℂ)-((ℓ : ℂ)*v+t))^2 ≠ 0 := by
      have hr : ℓ^2+(t-(ℓ*v+t))^2 ≠ 0 := by positivity
      exact_mod_cast hr
    field_simp [hℓc,hπ,hv,hd]
    ring
  have hinv (v : ℝ) : k v = ((Real.pi * ℓ : ℝ) : ℂ)⁻¹ * g (ℓ⁻¹*(v-t)) := by
    convert he (ℓ⁻¹*(v-t)) using 1
    congr 1
    field_simp [hℓ.ne']
    ring
  have hki : Integrable k := by
    have hi : Integrable (fun v : ℝ => g (ℓ⁻¹*(v-t))) := by
      simpa only [g, sub_eq_add_neg] using (hI.comp_mul_left' (inv_ne_zero hℓ.ne')).comp_add_right (-t)
    exact (hi.const_mul _).congr (Eventually.of_forall (fun v => (hinv v).symm))
  refine ⟨hki, ?_⟩
  change (∫ v : ℝ, k v) = _
  have hint : (∫ v : ℝ, k (ℓ*v+t)) = (ℓ⁻¹ : ℝ) • ∫ v : ℝ, k v := by
    rw [Measure.integral_comp_mul_left (fun v => k (v+t)) ℓ, integral_add_right_eq_self,
      abs_of_pos (inv_pos.mpr hℓ)]
  simp_rw [he] at hint
  rw [integral_const_mul] at hint
  change ((Real.pi * ℓ : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, g v) = _ at hint
  rw [show (∫ v : ℝ, g v) = (Real.pi : ℂ)*f (line ℓ t) from hE] at hint
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul] at hint
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hℓc,hπ] at hint
  linear_combination -hint

lemma weighted_complex_square_mean_le (p : ℝ → ℝ) (f : ℝ → ℂ)
    (hp : ∀ t, 0 ≤ p t) (hpi : Integrable p) (hpm : (∫ t, p t) = 1)
    (hfi : Integrable (fun t => (p t : ℂ)*f t))
    (hsi : Integrable (fun t => p t * ‖f t‖ ^ 2)) :
    ‖∫ t, (p t : ℂ)*f t‖ ^ 2 ≤ ∫ t, p t * ‖f t‖ ^ 2 := by
  let m := ∫ t, (p t : ℂ)*f t
  have hi : Integrable (fun t => (conj m * ((p t : ℂ)*f t)).re) := (hfi.const_mul (conj m)).re
  have he (t : ℝ) : p t * ‖f t - m‖ ^ 2 =
      p t * ‖f t‖ ^ 2 + p t * ‖m‖ ^ 2 - 2 * (conj m * ((p t : ℂ)*f t)).re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpos : 0 ≤ ∫ t, p t * ‖f t‖ ^ 2 + p t * ‖m‖ ^ 2 - 2 * (conj m * ((p t : ℂ)*f t)).re := by
    apply integral_nonneg
    intro t
    change 0 ≤ p t * ‖f t‖ ^ 2 + p t * ‖m‖ ^ 2 - 2 * (conj m * ((p t : ℂ)*f t)).re
    rw [← he]
    exact mul_nonneg (hp t) (sq_nonneg _)
  have hsum : Integrable (fun t => p t * ‖f t‖ ^ 2 + p t * ‖m‖ ^ 2) := hsi.add (hpi.mul_const _)
  rw [integral_sub hsum (hi.const_mul 2),
    integral_add hsi (hpi.mul_const _), integral_mul_const, hpm, one_mul, integral_const_mul] at hpos
  have hei : (∫ t, (conj m * ((p t : ℂ)*f t)).re) = (conj m*m).re := by
    have hh : (∫ t, (conj m * ((p t : ℂ)*f t)).re) = (∫ t, conj m * ((p t : ℂ)*f t)).re :=
      integral_re (hfi.const_mul (conj m))
    rw [hh, integral_const_mul]
  rw [hei, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hpos
  dsimp [m] at hpos
  linarith

lemma poissonKernelReal_weight_bound {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, poissonKernelReal ℓ (t-v) ≤ C / (1+v^2) := by
  let A : ℝ := 2 * (1+t^2+ℓ^2) / ℓ^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(ℓ / Real.pi) * A, by positivity, ?_⟩
  intro v
  have hp : 0 < ℓ^2+(t-v)^2 := by positivity
  have hv : 1+v^2 ≤ A*(ℓ^2+(t-v)^2) := by
    dsimp [A]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hℓ)).mpr
    have hbase : 1+v^2 ≤ 2*(1+t^2)+2*(t-v)^2 := by nlinarith [sq_nonneg (2*t-v)]
    have hm := mul_le_mul_of_nonneg_right hbase (sq_nonneg ℓ)
    nlinarith [mul_nonneg (show 0 ≤ 1+t^2 by positivity) (sq_nonneg (t-v)), sq_nonneg (ℓ^2)]
  unfold poissonKernelReal
  have hh := div_le_div_of_nonneg_left (show 0 ≤ ℓ / Real.pi by positivity)
    (show 0 < (1+v^2)/A from div_pos (by positivity) (by dsimp [A]; positivity))
    ((div_le_iff₀ (by dsimp [A]; positivity : 0 < A)).mpr (by simpa only [mul_comm] using hv))
  convert hh using 1 <;> field_simp <;> ring

lemma poissonKernelReal_translate_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    Integrable (fun v : ℝ => poissonKernelReal ℓ (t-v)) ∧
      (∫ v : ℝ, poissonKernelReal ℓ (t-v)) = 1 := by
  have he (v : ℝ) : poissonKernelReal ℓ (t-v) = poissonKernelReal ℓ (v-t) := by
    unfold poissonKernelReal
    congr 2
    ring
  constructor
  · apply ((poissonKernelReal_integral ℓ hℓ).1.comp_add_right (-t)).congr
    filter_upwards [] with v
    simpa only [sub_eq_add_neg] using (he v).symm
  · simp_rw [he]
    rw [integral_sub_right_eq_self]
    exact (poissonKernelReal_integral ℓ hℓ).2

lemma halfPlane_poisson_square_bound (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    (hb : ∃ R₀ B : ℝ, ∀ z : ℂ, R₀ ≤ z.re → ‖f z‖ ≤ B)
    (hI : Integrable (fun t : ℝ => ‖f (line 0 t)‖ ^ 2 / (1+t^2)))
    {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    Integrable (fun v : ℝ => poissonKernelReal ℓ (t-v) * ‖f (line 0 v)‖ ^ 2) ∧
      ‖f (line ℓ t)‖ ^ 2 ≤ ∫ v : ℝ, poissonKernelReal ℓ (t-v) * ‖f (line 0 v)‖ ^ 2 := by
  obtain ⟨hfi,hf⟩ := halfPlane_poisson f hd hg hb hℓ t
  have hc : Continuous (fun v : ℝ => f (line 0 v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (hd (line 0 v) (by simp [line])).continuousAt.comp
      (show ContinuousAt (fun v : ℝ => line 0 v) v by unfold line; fun_prop)
  have hi : Integrable (fun v : ℝ => poissonKernelReal ℓ (t-v) * ‖f (line 0 v)‖ ^ 2) := by
    obtain ⟨C,hC,hbound⟩ := poissonKernelReal_weight_bound hℓ t
    refine (hI.const_mul C).mono' ?_ ?_
    · exact (((poissonKernelReal_continuous ℓ hℓ).comp (continuous_const.sub continuous_id)).mul
        (hc.norm.pow 2)).aestronglyMeasurable
    · filter_upwards [] with v
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold poissonKernelReal; positivity)]
      convert mul_le_mul_of_nonneg_right (hbound v) (sq_nonneg ‖f (line 0 v)‖) using 1 <;> ring
  refine ⟨hi, ?_⟩
  rw [← hf]
  exact weighted_complex_square_mean_le (fun v => poissonKernelReal ℓ (t-v)) (fun v => f (line 0 v))
    (fun v => (poissonKernelReal_bounds ℓ hℓ (t-v)).1)
    (poissonKernelReal_translate_integral hℓ t).1 (poissonKernelReal_translate_integral hℓ t).2 hfi hi

end LiLiuGoldbach16
