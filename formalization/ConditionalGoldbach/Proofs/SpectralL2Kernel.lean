import ConditionalGoldbach.Proofs.SpectralHilbertSchmidtCompact

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- The squared norm of a scalar L² class is the integral of its pointwise squared norm. -/
theorem l2Kernel_norm_sq_integral (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- An L² row acts boundedly on L² by the un-conjugated integral pairing. -/
theorem l2Kernel_row_bound {k : β → ℂ} (hk : MemLp k 2 ν) (f : Lp ℂ 2 ν) :
    Integrable (fun y => k y * f y) ν ∧
      ‖∫ y, k y * f y ∂ν‖ ^ 2 ≤ (∫ y, ‖k y‖ ^ 2 ∂ν) * ‖f‖ ^ 2 := by
  have hi : Integrable (fun y => k y * f y) ν :=
    memLp_one_iff_integrable.mp (hk.fun_mul (Lp.memLp f))
  let g : Lp ℂ 2 ν := hk.star.toLp (star k)
  have heq : (∫ y, k y * f y ∂ν) = inner ℂ g f := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk.star.coeFn_toLp] with y hy
    change k y * f y = inner ℂ ((hk.star.toLp (star k)) y) (f y)
    rw [hy]
    change k y * f y = f y * star (star (k y))
    simp only [star_star, mul_comm]
  have hg : ‖g‖ ^ 2 = ∫ y, ‖k y‖ ^ 2 ∂ν := by
    rw [l2Kernel_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hk.star.coeFn_toLp] with y hy
    change ‖(hk.star.toLp (star k)) y‖ ^ 2 = _
    rw [hy]
    simp only [Pi.star_apply, norm_star]
  refine ⟨hi, ?_⟩
  rw [heq, ← hg]
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) g f) 2

variable [SFinite μ] [SFinite ν]

/-- Almost every section of an L² product kernel is an L² row. -/
theorem l2Kernel_rows_memLp {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 ν := by
  filter_upwards [hK.aestronglyMeasurable.prodMk_left, hK.norm.integrable_sq.prod_right_ae] with x hx hi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hi

/-- Applying a square-integrable kernel to an L² class again gives an L² function. -/
theorem l2Kernel_apply_memLp {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) : MemLp (fun x => ∫ y, K (x, y) * f y ∂ν) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => ∫ y, K (x, y) * f y ∂ν) μ :=
    (hK.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply Integrable.mono' (hK.norm.integrable_sq.integral_prod_left.mul_const (‖f‖ ^ 2))
    (hm.norm.pow 2)
  filter_upwards [l2Kernel_rows_memLp hK] with x hx
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using (l2Kernel_row_bound hx f).2

/-- The L² class obtained by applying the integral kernel. -/
def l2KernelApply {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) : Lp ℂ 2 μ :=
  (l2Kernel_apply_memLp hK f).toLp (fun x => ∫ y, K (x, y) * f y ∂ν)

/-- The defining integral formula holds almost everywhere. -/
theorem l2KernelApply_coeFn {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    (l2KernelApply hK f : α → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * f y ∂ν :=
  (l2Kernel_apply_memLp hK f).coeFn_toLp

/-- The kernel L² norm bounds the squared output norm. -/
theorem l2KernelApply_norm_sq_le {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    ‖l2KernelApply hK f‖ ^ 2 ≤ (∫ p, ‖K p‖ ^ 2 ∂(μ.prod ν)) * ‖f‖ ^ 2 := by
  rw [l2Kernel_norm_sq_integral]
  calc
    (∫ x, ‖l2KernelApply hK f x‖ ^ 2 ∂μ) =
        ∫ x, ‖∫ y, K (x, y) * f y ∂ν‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [l2KernelApply_coeFn hK f] with x hx
      rw [hx]
    _ ≤ ∫ x, (∫ y, ‖K (x, y)‖ ^ 2 ∂ν) * ‖f‖ ^ 2 ∂μ := by
      apply integral_mono_ae (l2Kernel_apply_memLp hK f).norm.integrable_sq
        (hK.norm.integrable_sq.integral_prod_left.mul_const (‖f‖ ^ 2))
      filter_upwards [l2Kernel_rows_memLp hK] with x hx
      exact (l2Kernel_row_bound hx f).2
    _ = _ := by rw [integral_mul_const, ← integral_prod _ hK.norm.integrable_sq]

/-- Linearity of the kernel action on equivalence classes. -/
def l2KernelLinearMap {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν)) :
    Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := l2KernelApply hK
  map_add' f g := by
    apply Lp.ext
    filter_upwards [l2KernelApply_coeFn hK (f + g), l2KernelApply_coeFn hK f,
      l2KernelApply_coeFn hK g, Lp.coeFn_add (l2KernelApply hK f) (l2KernelApply hK g),
      l2Kernel_rows_memLp hK] with x hfg hf hg hout hx
    rw [hfg, hout]
    change (∫ y, K (x, y) * (f + g) y ∂ν) = l2KernelApply hK f x + l2KernelApply hK g x
    rw [hf, hg, ← integral_add (l2Kernel_row_bound hx f).1 (l2Kernel_row_bound hx g).1]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy]
    exact mul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [l2KernelApply_coeFn hK (c • f), l2KernelApply_coeFn hK f,
      Lp.coeFn_smul c (l2KernelApply hK f)] with x hcf hf hout
    simp only [RingHom.id_apply]
    rw [hcf, hout]
    change (∫ y, K (x, y) * (c • f) y ∂ν) = c * l2KernelApply hK f x
    rw [hf, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy]
    change K (x, y) * (c * f y) = c * (K (x, y) * f y)
    ring

/-- A square-integrable kernel defines a bounded continuous linear map. -/
def l2KernelOperator {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν)) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (l2KernelLinearMap hK).mkContinuous (Real.sqrt (∫ p, ‖K p‖ ^ 2 ∂(μ.prod ν))) (by
    intro f
    have hn : 0 ≤ ∫ p, ‖K p‖ ^ 2 ∂(μ.prod ν) := integral_nonneg (fun _ => sq_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [l2KernelLinearMap, LinearMap.coe_mk, AddHom.coe_mk, mul_pow, Real.sq_sqrt hn] using l2KernelApply_norm_sq_le hK f)

/-- The bounded integral operator retains the original pointwise integral formula. -/
theorem l2KernelOperator_coeFn {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 ν) :
    (l2KernelOperator hK f : α → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * f y ∂ν :=
  l2KernelApply_coeFn hK f

/-- Operator norm bound by the square-integral of the actual kernel. -/
theorem l2KernelOperator_norm_le {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν)) :
    ‖l2KernelOperator hK‖ ≤ Real.sqrt (∫ p, ‖K p‖ ^ 2 ∂(μ.prod ν)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  have hn : 0 ≤ ∫ p, ‖K p‖ ^ 2 ∂(μ.prod ν) := integral_nonneg (fun _ => sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [l2KernelOperator, LinearMap.mkContinuous_apply, l2KernelLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, mul_pow, Real.sq_sqrt hn] using l2KernelApply_norm_sq_le hK f

end ConditionalGoldbach
