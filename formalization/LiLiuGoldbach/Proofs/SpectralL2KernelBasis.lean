import LiLiuGoldbach.Proofs.SpectralL2Kernel

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- Rowwise Parseval for the actual un-conjugated integral kernel pairing. -/
theorem l2Kernel_row_parseval {k : β → ℂ} (hk : MemLp k 2 ν)
    (b : HilbertBasis ℕ ℂ (Lp ℂ 2 ν)) :
    HasSum (fun j => ‖∫ y, k y * b j y ∂ν‖ ^ 2) (∫ y, ‖k y‖ ^ 2 ∂ν) := by
  let g : Lp ℂ 2 ν := hk.star.toLp (star k)
  have heq (j : ℕ) : (∫ y, k y * b j y ∂ν) = inner ℂ g (b j) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk.star.coeFn_toLp] with y hy
    change k y * b j y = inner ℂ ((hk.star.toLp (star k)) y) (b j y)
    rw [hy]
    change k y * b j y = b j y * star (star (k y))
    simp only [star_star, mul_comm]
  have hg : ‖g‖ ^ 2 = ∫ y, ‖k y‖ ^ 2 ∂ν := by
    rw [l2Kernel_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hk.star.coeFn_toLp] with y hy
    change ‖(hk.star.toLp (star k)) y‖ ^ 2 = _
    rw [hy]
    simp only [Pi.star_apply, norm_star]
  simpa only [heq, norm_inner_symm, hg] using hilbertBasis_hasSum_sq_inner b g

variable [SFinite μ] [SFinite ν]

/-- The sum of squared norms of the images of any Hilbert basis is exactly the kernel energy. -/
theorem l2KernelOperator_hasSum_norm_sq {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (b : HilbertBasis ℕ ℂ (Lp ℂ 2 ν)) :
    HasSum (fun j => ‖l2KernelOperator hK (b j)‖ ^ 2)
      (∫ p, ‖K p‖ ^ 2 ∂(μ.prod ν)) := by
  let F : ℕ → α → ℝ := fun j x => ‖l2KernelOperator hK (b j) x‖ ^ 2
  let E : α → ℝ := fun x => ∫ y, ‖K (x, y)‖ ^ 2 ∂ν
  have hcoe : ∀ᵐ x ∂μ, ∀ j, l2KernelOperator hK (b j) x = ∫ y, K (x, y) * b j y ∂ν :=
    ae_all_iff.mpr fun j => l2KernelOperator_coeFn hK (b j)
  have hp : ∀ᵐ x ∂μ, HasSum (fun j => F j x) (E x) := by
    filter_upwards [hcoe, l2Kernel_rows_memLp hK] with x hx hk
    simpa only [F, E, hx] using l2Kernel_row_parseval hk b
  have hm (j : ℕ) : AEStronglyMeasurable (F j) μ :=
    (Lp.aestronglyMeasurable (l2KernelOperator hK (b j))).norm.pow 2
  have hi : Integrable (fun x => ∑' j, F j x) μ := by
    apply hK.norm.integrable_sq.integral_prod_left.congr
    filter_upwards [hp] with x hx
    exact hx.tsum_eq.symm
  have hsum := hasSum_integral_of_dominated_convergence F hm
    (fun j => Filter.Eventually.of_forall fun x => by
      simp only [F, Real.norm_eq_abs, abs_pow, abs_norm, le_refl])
    (hp.mono fun x hx => hx.summable) hi hp
  convert hsum using 1
  · funext j
    exact l2Kernel_norm_sq_integral _
  · exact integral_prod _ hK.norm.integrable_sq

/-- The integral operator is Hilbert--Schmidt whenever the ambient L² space has the paper's basis. -/
theorem l2KernelOperator_isHilbertSchmidt {K : α × α → ℂ} (hK : MemLp K 2 (μ.prod μ))
    (b : HilbertBasis ℕ ℂ (Lp ℂ 2 μ)) : IsHilbertSchmidt (l2KernelOperator hK) :=
  ⟨b, (l2KernelOperator_hasSum_norm_sq hK b).summable⟩

/-- The Hilbert--Schmidt norm is exactly the L² norm of the kernel. -/
theorem l2KernelOperator_hsNorm_sq {K : α × α → ℂ} (hK : MemLp K 2 (μ.prod μ))
    (b : HilbertBasis ℕ ℂ (Lp ℂ 2 μ)) :
    hsNorm (l2KernelOperator hK) ^ 2 = ∫ p, ‖K p‖ ^ 2 ∂(μ.prod μ) := by
  rw [(proposition_5_3_hs_basis_independent _ (l2KernelOperator_isHilbertSchmidt hK b) b).2]
  exact (l2KernelOperator_hasSum_norm_sq hK b).tsum_eq

end LiLiuGoldbach16
