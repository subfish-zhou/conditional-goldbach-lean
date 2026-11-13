import LiLiuGoldbach.Definitions

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

/-- Scaling the Poisson density reduces it to the integrable Cauchy kernel. -/
theorem poissonKernelReal_scaled (a : ℝ) (ha : 0 < a) (t : ℝ) :
    poissonKernelReal a t = (1 / (Real.pi * a)) * (1 + (a⁻¹ * t) ^ 2)⁻¹ := by
  have h₁ : a ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _))
  have h₂ : 1 + (a⁻¹ * t) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold poissonKernelReal
  field_simp [ha.ne', Real.pi_ne_zero, h₁, h₂]

/-- The Poisson density is integrable and has total mass one. -/
theorem poissonKernelReal_integral (a : ℝ) (ha : 0 < a) :
    Integrable (poissonKernelReal a) ∧ (∫ t : ℝ, poissonKernelReal a t) = 1 := by
  have heq : poissonKernelReal a = fun t => (1 / (Real.pi * a)) * (1 + (a⁻¹ * t) ^ 2)⁻¹ :=
    funext (poissonKernelReal_scaled a ha)
  rw [heq]
  refine ⟨(integrable_inv_one_add_mul_sq (inv_ne_zero ha.ne')).const_mul _, ?_⟩
  rw [integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr ha)]
  field_simp [ha.ne', Real.pi_ne_zero]

/-- The exact Poisson-action specification in Lemma 6.4. -/
theorem lemma_6_4_poisson_action_spec :
    (∀ f : ℝ → ℝ, poissonAction 0 f = f) ∧
    ∀ ℓ : ℝ, 0 < ℓ →
      Integrable (poissonKernelReal ℓ) ∧
      (∀ t : ℝ, 0 ≤ poissonKernelReal ℓ t) ∧
      (∫ t : ℝ, poissonKernelReal ℓ t) = 1 ∧
      ∀ f : ℝ → ℝ,
        poissonAction ℓ f = realConvolution (poissonKernelReal ℓ) f := by
  refine ⟨fun f => by simp [poissonAction], fun ℓ hℓ => ?_⟩
  obtain ⟨hi, hm⟩ := poissonKernelReal_integral ℓ hℓ
  exact ⟨hi, fun t => by unfold poissonKernelReal; positivity, hm,
    fun f => ite_eq_right hℓ.ne'⟩

/-- The smoothed Perron kernel is meromorphic, with residue one at the origin. -/
theorem lemma_6_4_perron_residue (X : ℝ) (hX : 1 < X) :
    MeromorphicOn (smoothedPerronKernel X) Set.univ ∧
    Tendsto (fun v : ℂ => v * smoothedPerronKernel X v)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have hXp : 0 < X := lt_trans zero_lt_one hX
  have hS : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
  have hXc : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hXp.ne'
  have hSc : (Real.sqrt X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hlog : Real.log (Real.sqrt X) ≠ 0 := by
    rw [Real.log_sqrt hXp.le]
    exact div_ne_zero (Real.log_pos hX).ne' (by norm_num)
  have hlogc : (Real.log (Real.sqrt X) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  constructor
  · intro z hz
    have hx : AnalyticAt ℂ (fun v : ℂ => (X : ℂ) ^ v) z := by
      simp only [Complex.cpow_def_of_ne_zero hXc]
      exact (analyticAt_const.mul analyticAt_id).cexp'
    have hs : AnalyticAt ℂ (fun v : ℂ => (Real.sqrt X : ℂ) ^ v) z := by
      simp only [Complex.cpow_def_of_ne_zero hSc]
      exact (analyticAt_const.mul analyticAt_id).cexp'
    exact (hx.sub hs).meromorphicAt.div ((analyticAt_id.pow 2).mul analyticAt_const).meromorphicAt
  · have hd := (Complex.hasStrictDerivAt_const_cpow (y := (0 : ℂ)) (Or.inl hXc)).hasDerivAt.sub
      ((Complex.hasStrictDerivAt_const_cpow (y := (0 : ℂ)) (Or.inl hSc)).hasDerivAt)
    have ht := hd.tendsto_slope_zero.div_const (Real.log (Real.sqrt X) : ℂ)
    have hl : (Complex.log (X : ℂ) - Complex.log (Real.sqrt X : ℂ)) /
        (Real.log (Real.sqrt X) : ℂ) = 1 := by
      rw [← Complex.ofReal_log hXp.le, ← Complex.ofReal_log hS.le, Real.log_sqrt hXp.le]
      push_cast
      field_simp [(Real.log_pos hX).ne']
      ring
    simp only [Pi.sub_apply, zero_add, Complex.cpow_zero, one_mul, sub_self, sub_zero, smul_eq_mul, hl] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv' : v ≠ 0 := hv
    unfold smoothedPerronKernel
    field_simp [hv', hlogc]

end LiLiuGoldbach16
