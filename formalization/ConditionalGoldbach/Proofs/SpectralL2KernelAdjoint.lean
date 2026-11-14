module

public import Mathlib.MeasureTheory.Function.L2Space
public import ConditionalGoldbach.Proofs.SpectralL2Kernel

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- Products of two scalar L² functions on separate variables remain L². -/
theorem l2Kernel_product_memLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun p : α × β => conj (f p.1) * g p.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × β => conj (f p.1) * g p.2) (μ.prod ν) :=
    ((Lp.aestronglyMeasurable f).comp_fst.star).mul (Lp.aestronglyMeasurable g).comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [norm_mul, Complex.norm_conj, mul_pow] using
    (Lp.memLp f).norm.integrable_sq.mul_prod (Lp.memLp g).norm.integrable_sq

/-- The mixed kernel pairing is absolutely integrable on the product measure. -/
theorem l2Kernel_pairing_integrable [SFinite μ] [SFinite ν]
    {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    Integrable (fun p : α × β => conj (f p.1) * K p * g p.2) (μ.prod ν) := by
  have hi := memLp_one_iff_integrable.mp (hK.fun_mul (l2Kernel_product_memLp f g))
  convert hi using 1
  funext p
  ring

variable [SFinite μ] [SFinite ν]

/-- The bounded integral operator has the expected product-integral sesquilinear pairing. -/
theorem l2KernelOperator_pairing {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    inner ℂ f (l2KernelOperator hK g) =
      ∫ p : α × β, conj (f p.1) * K p * g p.2 ∂(μ.prod ν) := by
  rw [L2.inner_def, integral_prod _ (l2Kernel_pairing_integrable hK f g)]
  apply integral_congr_ae
  filter_upwards [l2KernelOperator_coeFn hK g] with x hx
  rw [hx]
  change (∫ y, K (x, y) * g y ∂ν) * conj (f x) = _
  rw [mul_comm, ← integral_const_mul]
  congr 1
  funext y
  ring

/-- An almost-everywhere Hermitian square-integrable kernel defines a self-adjoint operator. -/
theorem l2KernelOperator_isSelfAdjoint {K : α × α → ℂ} (hK : MemLp K 2 (μ.prod μ))
    (hherm : ∀ᵐ p ∂(μ.prod μ), K p.swap = conj (K p)) :
    IsSelfAdjoint (l2KernelOperator hK) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (l2KernelOperator hK f) g = inner ℂ f (l2KernelOperator hK g)
  rw [← inner_conj_symm (𝕜 := ℂ) (l2KernelOperator hK f) g,
    l2KernelOperator_pairing hK g f, l2KernelOperator_pairing hK f g, ← integral_conj]
  rw [← integral_prod_swap (fun p : α × α => conj (f p.1) * K p * g p.2)]
  apply integral_congr_ae
  filter_upwards [hherm] with p hp
  simp only [map_mul, Complex.conj_conj, Prod.fst_swap, Prod.snd_swap]
  rw [hp]
  ring

end ConditionalGoldbach
