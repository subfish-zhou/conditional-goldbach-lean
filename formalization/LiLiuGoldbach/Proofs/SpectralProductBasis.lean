import LiLiuGoldbach.Proofs.SpectralHilbertSchmidt

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Reindex a Hilbert basis without changing any of its vectors. -/
def hilbertBasisReindex {ι κ : Type*} (b : HilbertBasis ι ℂ E) (e : κ ≃ ι) :
    HilbertBasis κ ℂ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (b ∘ e) = Set.range b := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, congrArg b (e.apply_symm_apply i)⟩
    rw [hr, b.dense_span])

@[simp] theorem hilbertBasisReindex_apply {ι κ : Type*} (b : HilbertBasis ι ℂ E)
    (e : κ ≃ ι) (j : κ) : hilbertBasisReindex b e j = b (e j) :=
  congrFun (HilbertBasis.coe_mk _ _) j

/-- The orthogonal sum of two Hilbert bases is a Hilbert basis. -/
def hilbertBasisProd (b : HilbertBasis ℕ ℂ E) (c : HilbertBasis ℕ ℂ F) :
    HilbertBasis (ℕ ⊕ ℕ) ℂ (WithLp 2 (E × F)) := by
  let v : ℕ ⊕ ℕ → WithLp 2 (E × F) := Sum.elim
    (fun j => WithLp.toLp 2 (b j, 0)) (fun j => WithLp.toLp 2 (0, c j))
  have hv : Orthonormal ℂ v := by
    apply orthonormal_iff_ite.mpr
    intro i j
    cases i <;> cases j <;>
      simp [v, WithLp.prod_inner_apply, orthonormal_iff_ite.mp b.orthonormal,
        orthonormal_iff_ite.mp c.orthonormal]
  have hspan : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hx₁ : x.fst = 0 := by
      apply b.repr.injective
      apply lp.ext
      funext j
      simp only [HilbertBasis.repr_apply_apply, inner_zero_right]
      have hh := hx (v (Sum.inl j)) (Submodule.subset_span (Set.mem_range_self (Sum.inl j)))
      simpa only [v, Sum.elim_inl, WithLp.prod_inner_apply, WithLp.ofLp_toLp, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_zero_left, add_zero] using hh
    have hx₂ : x.snd = 0 := by
      apply c.repr.injective
      apply lp.ext
      funext j
      simp only [HilbertBasis.repr_apply_apply, inner_zero_right]
      have hh := hx (v (Sum.inr j)) (Submodule.subset_span (Set.mem_range_self (Sum.inr j)))
      simpa only [v, Sum.elim_inr, WithLp.prod_inner_apply, WithLp.ofLp_toLp, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_zero_left, zero_add] using hh
    change x = 0
    apply (WithLp.equiv 2 (E × F)).injective
    exact Prod.ext hx₁ hx₂
  exact HilbertBasis.mkOfOrthogonalEqBot hv hspan

@[simp] theorem hilbertBasisProd_inl (b : HilbertBasis ℕ ℂ E) (c : HilbertBasis ℕ ℂ F) (j : ℕ) :
    hilbertBasisProd b c (Sum.inl j) = WithLp.toLp 2 (b j, 0) := by
  unfold hilbertBasisProd
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

@[simp] theorem hilbertBasisProd_inr (b : HilbertBasis ℕ ℂ E) (c : HilbertBasis ℕ ℂ F) (j : ℕ) :
    hilbertBasisProd b c (Sum.inr j) = WithLp.toLp 2 (0, c j) := by
  unfold hilbertBasisProd
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

/-- A fixed bijection turns the two countable blocks into the paper's natural-number convention. -/
def sumNatEnumeration : ℕ ≃ ℕ ⊕ ℕ := Classical.choice inferInstance

def hilbertBasisProdNat (b : HilbertBasis ℕ ℂ E) (c : HilbertBasis ℕ ℂ F) :
    HilbertBasis ℕ ℂ (WithLp 2 (E × F)) :=
  hilbertBasisReindex (hilbertBasisProd b c) sumNatEnumeration

end LiLiuGoldbach16
