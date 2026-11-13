import ConditionalGoldbach.Proofs.SpectralL2KernelBasis
import ConditionalGoldbach.Proofs.SpectralL2KernelAdjoint
import ConditionalGoldbach.Proofs.SpectralProductBasis

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

abbrev BoundaryL2 := Lp ℂ 2 (volume : Measure ℝ)
abbrev BoundaryL2Pair := WithLp 2 (BoundaryL2 × BoundaryL2)

/-- The actual two-by-two operator on the orthogonal sum of the two vertical boundaries. -/
def boundaryBlockOperator (A B C D : BoundaryL2 →L[ℂ] BoundaryL2) :
    BoundaryL2Pair →L[ℂ] BoundaryL2Pair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ BoundaryL2 BoundaryL2).symm.toContinuousLinearMap ∘L
    ((A ∘L WithLp.fstL 2 ℂ BoundaryL2 BoundaryL2 +
      B ∘L WithLp.sndL 2 ℂ BoundaryL2 BoundaryL2).prod
     (C ∘L WithLp.fstL 2 ℂ BoundaryL2 BoundaryL2 +
      D ∘L WithLp.sndL 2 ℂ BoundaryL2 BoundaryL2))

@[simp] theorem boundaryBlockOperator_fst (A B C D : BoundaryL2 →L[ℂ] BoundaryL2)
    (f : BoundaryL2Pair) : (boundaryBlockOperator A B C D f).fst = A f.fst + B f.snd := rfl

@[simp] theorem boundaryBlockOperator_snd (A B C D : BoundaryL2 →L[ℂ] BoundaryL2)
    (f : BoundaryL2Pair) : (boundaryBlockOperator A B C D f).snd = C f.fst + D f.snd := rfl

/-- The four square-integrable boundary blocks determine a bounded operator, with no extra factor. -/
def boundaryKernelOperator (a b : ℝ) (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume) :
    BoundaryL2Pair →L[ℂ] BoundaryL2Pair :=
  boundaryBlockOperator
    (l2KernelOperator (hK a (by simp) a (by simp)))
    (l2KernelOperator (hK a (by simp) b (by simp)))
    (l2KernelOperator (hK b (by simp) a (by simp)))
    (l2KernelOperator (hK b (by simp) b (by simp)))

/-- Both rows of the boundary operator equal the two integrals in the paper's convention. -/
theorem boundaryKernelOperator_coeFn (a b : ℝ) (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (f : BoundaryL2Pair) :
    ((boundaryKernelOperator a b K hK f).fst : ℝ → ℂ) =ᵐ[volume]
      (fun t => (∫ u, K (line a t) (line a u) * f.fst u) +
        ∫ u, K (line a t) (line b u) * f.snd u) ∧
    ((boundaryKernelOperator a b K hK f).snd : ℝ → ℂ) =ᵐ[volume]
      (fun t => (∫ u, K (line b t) (line a u) * f.fst u) +
        ∫ u, K (line b t) (line b u) * f.snd u) := by
  constructor
  · filter_upwards [Lp.coeFn_add (l2KernelOperator (hK a (by simp) a (by simp)) f.fst)
        (l2KernelOperator (hK a (by simp) b (by simp)) f.snd),
      l2KernelOperator_coeFn (hK a (by simp) a (by simp)) f.fst,
      l2KernelOperator_coeFn (hK a (by simp) b (by simp)) f.snd] with t hadd h₁ h₂
    exact hadd.trans (congrArg₂ (· + ·) h₁ h₂)
  · filter_upwards [Lp.coeFn_add (l2KernelOperator (hK b (by simp) a (by simp)) f.fst)
        (l2KernelOperator (hK b (by simp) b (by simp)) f.snd),
      l2KernelOperator_coeFn (hK b (by simp) a (by simp)) f.fst,
      l2KernelOperator_coeFn (hK b (by simp) b (by simp)) f.snd] with t hadd h₁ h₂
    exact hadd.trans (congrArg₂ (· + ·) h₁ h₂)

/-- The four kernel energies sum to the Hilbert--Schmidt square sum of the boundary operator. -/
theorem boundaryKernelOperator_hasSum_norm_sq (a b : ℝ) (hab : a ≠ b) (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (c : HilbertBasis ℕ ℂ BoundaryL2) :
    HasSum (fun j => ‖boundaryKernelOperator a b K hK (hilbertBasisProdNat c c j)‖ ^ 2)
      (BoundaryKernelSquareIntegral a b K) := by
  let A := boundaryKernelOperator a b K hK
  have hleft : HasSum (fun j => ‖A (hilbertBasisProd c c (Sum.inl j))‖ ^ 2)
      ((∫ p : ℝ × ℝ, ‖K (line a p.1) (line a p.2)‖ ^ 2) +
       ∫ p : ℝ × ℝ, ‖K (line b p.1) (line a p.2)‖ ^ 2) := by
    have hh := (l2KernelOperator_hasSum_norm_sq (hK a (by simp) a (by simp)) c).add
      (l2KernelOperator_hasSum_norm_sq (hK b (by simp) a (by simp)) c)
    simpa only [hilbertBasisProd_inl, WithLp.prod_norm_sq_eq_of_L2, A, boundaryKernelOperator,
      boundaryBlockOperator_fst, boundaryBlockOperator_snd, WithLp.toLp_fst, WithLp.toLp_snd,
      map_zero, add_zero, MeasureTheory.Measure.volume_eq_prod] using hh
  have hright : HasSum (fun j => ‖A (hilbertBasisProd c c (Sum.inr j))‖ ^ 2)
      ((∫ p : ℝ × ℝ, ‖K (line a p.1) (line b p.2)‖ ^ 2) +
       ∫ p : ℝ × ℝ, ‖K (line b p.1) (line b p.2)‖ ^ 2) := by
    have hh := (l2KernelOperator_hasSum_norm_sq (hK a (by simp) b (by simp)) c).add
      (l2KernelOperator_hasSum_norm_sq (hK b (by simp) b (by simp)) c)
    simpa only [hilbertBasisProd_inr, WithLp.prod_norm_sq_eq_of_L2, A, boundaryKernelOperator,
      boundaryBlockOperator_fst, boundaryBlockOperator_snd, WithLp.toLp_fst, WithLp.toLp_snd,
      map_zero, zero_add, MeasureTheory.Measure.volume_eq_prod] using hh
  have hs : HasSum (fun j : ℕ ⊕ ℕ => ‖A (hilbertBasisProd c c j)‖ ^ 2)
      (BoundaryKernelSquareIntegral a b K) := by
    convert HasSum.sum (f := fun j : ℕ ⊕ ℕ => ‖A (hilbertBasisProd c c j)‖ ^ 2) hleft hright using 1
    unfold BoundaryKernelSquareIntegral
    simp only [Finset.sum_pair hab]
    simp only [MeasureTheory.Measure.volume_eq_prod]
    rw [integral_prod _ (hK a (by simp) a (by simp)).norm.integrable_sq,
      integral_prod _ (hK a (by simp) b (by simp)).norm.integrable_sq,
      integral_prod _ (hK b (by simp) a (by simp)).norm.integrable_sq,
      integral_prod _ (hK b (by simp) b (by simp)).norm.integrable_sq]
    ring
  simpa only [hilbertBasisProdNat, hilbertBasisReindex_apply, Function.comp_def, A] using
    sumNatEnumeration.hasSum_iff.mpr hs

/-- The exact boundary-kernel square integral is the boundary operator's squared HS norm. -/
theorem boundaryKernelOperator_hilbertSchmidt (a b : ℝ) (hab : a ≠ b) (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (c : HilbertBasis ℕ ℂ BoundaryL2) :
    IsHilbertSchmidt (boundaryKernelOperator a b K hK) ∧
      hsNorm (boundaryKernelOperator a b K hK) ^ 2 = BoundaryKernelSquareIntegral a b K := by
  have hs := boundaryKernelOperator_hasSum_norm_sq a b hab K hK c
  have hHS : IsHilbertSchmidt (boundaryKernelOperator a b K hK) :=
    ⟨hilbertBasisProdNat c c, hs.summable⟩
  exact ⟨hHS, (proposition_5_3_hs_basis_independent _ hHS _).2.trans hs.tsum_eq⟩

/-- Transposed conjugate kernels give adjoint cross-blocks. -/
theorem l2Kernel_cross_adjoint {K L : ℝ × ℝ → ℂ}
    (hK : MemLp K 2 volume) (hL : MemLp L 2 volume)
    (hherm : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), L p.swap = conj (K p))
    (f g : BoundaryL2) :
    inner ℂ (l2KernelOperator hK f) g = inner ℂ f (l2KernelOperator hL g) := by
  rw [← inner_conj_symm (𝕜 := ℂ) (l2KernelOperator hK f) g,
    l2KernelOperator_pairing hK g f, l2KernelOperator_pairing hL f g, ← integral_conj]
  rw [← integral_prod_swap (fun p : ℝ × ℝ => conj (f p.1) * L p * g p.2)]
  apply integral_congr_ae
  filter_upwards [hherm] with p hp
  simp only [map_mul, Complex.conj_conj, Prod.fst_swap, Prod.snd_swap]
  rw [hp]
  ring

/-- Hermitian symmetry of the actual boundary kernel makes the four-block operator self-adjoint. -/
theorem boundaryKernelOperator_isSelfAdjoint (a b : ℝ) (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hherm : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ), ∀ t u : ℝ,
      K (line y u) (line x t) = conj (K (line x t) (line y u))) :
    IsSelfAdjoint (boundaryKernelOperator a b K hK) := by
  have hp (x : ℝ) (hx : x ∈ ({a, b} : Finset ℝ)) (y : ℝ) (hy : y ∈ ({a, b} : Finset ℝ))
      (f g : BoundaryL2) :
      inner ℂ (l2KernelOperator (hK x hx y hy) f) g =
        inner ℂ f (l2KernelOperator (hK y hy x hx) g) := by
    apply l2Kernel_cross_adjoint
    exact Filter.Eventually.of_forall fun p => hherm x hx y hy p.1 p.2
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (boundaryKernelOperator a b K hK f) g =
    inner ℂ f (boundaryKernelOperator a b K hK g)
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    boundaryKernelOperator, boundaryBlockOperator_fst, boundaryBlockOperator_snd,
    inner_add_left, inner_add_right,
    hp a (by simp) a (by simp), hp a (by simp) b (by simp),
    hp b (by simp) a (by simp), hp b (by simp) b (by simp)]
  ring

end ConditionalGoldbach
