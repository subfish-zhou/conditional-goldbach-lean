module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import ConditionalGoldbach.Proofs.SpectralHilbertSchmidt
public import ConditionalGoldbach.Proofs.SpectralPositiveTrace
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compact self-adjoint spectral theorem, with an initially arbitrary index type. -/
theorem compact_symmetric_exists_eigenbasis (T : H →L[ℂ] H)
    (hc : IsCompactOperator T) (hs : T.IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ H) (μ : ι → ℝ),
      ∀ j, T (b j) = (μ j : ℂ) • b j := by
  let E : ℂ → Submodule ℂ H := fun z => Module.End.eigenspace T.toLinearMap z
  have he (z : ℂ) : CompleteSpace (E z) := inferInstance
  choose w b hb using fun z : ℂ => exists_hilbertBasis ℂ (E z)
  let ι := (Σ z : ℂ, w z)
  let v : ι → H := fun j => (b j.1 j.2 : H)
  have hv : Orthonormal ℂ v :=
    hs.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal (fun z => (b z).orthonormal)
  have hspan : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ (⨆ z, E z)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro z
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hz (j : w z) : inner ℂ x (b z j : H) = 0 := by
        exact (Submodule.mem_orthogonal' _ _).mp hx (v ⟨z, j⟩)
          (Submodule.subset_span (Set.mem_range_self (⟨z, j⟩ : ι)))
      have hsum := (innerSL ℂ x).hasSum ((E z).subtypeL.hasSum ((b z).hasSum_repr ⟨y, hy⟩))
      have hzero : HasSum (fun _ : w z => (0 : ℂ)) (inner ℂ x y) := by
        simpa only [map_smul, innerSL_apply_apply, Submodule.subtypeL_apply, hz, smul_zero] using hsum
      exact hzero.unique hasSum_zero
    simpa only [E, ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] using hx'
  let B : HilbertBasis ι ℂ H := HilbertBasis.mkOfOrthogonalEqBot hv hspan
  have hB (j : ι) : B j = v j := by
    exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hv hspan) j
  refine ⟨ι, B, fun j => j.1.re, ?_⟩
  intro j
  have heig : T (v j) = j.1 • v j := (Module.End.mem_eigenspace_iff).mp (b j.1 j.2).property
  have hn : v j ≠ 0 := hv.ne_zero j
  have hr : conj j.1 = j.1 := hs.conj_eigenvalue_eq_self
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨(b j.1 j.2).property, hn⟩)
  rw [hB, heig, ← Complex.conj_eq_iff_re.mp hr]

omit [CompleteSpace H] in
/-- A Hilbert basis has countable index whenever the space admits a countable Hilbert basis. -/
theorem hilbertBasis_countable_index {ι : Type*} (b : HilbertBasis ℕ ℂ H)
    (c : HilbertBasis ι ℂ H) : Countable ι := by
  let f : ℕ → ι → ℂ := fun j i => inner ℂ (b j) (c i) * inner ℂ (c i) (b j)
  have hf (j : ℕ) : (Function.support (f j)).Countable :=
    (c.summable_inner_mul_inner (b j) (b j)).countable_support
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion hf).mono
  intro i hi
  simp only [Set.mem_iUnion, Function.mem_support]
  by_contra! hn
  have hz : c i = 0 := by
    apply b.repr.injective
    apply lp.ext
    funext j
    simp only [HilbertBasis.repr_apply_apply, inner_zero_right]
    rcases mul_eq_zero.mp (hn j) with h | h
    · exact h
    · exact inner_eq_zero_symm.mp h
  exact c.orthonormal.ne_zero i hz

omit [CompleteSpace H] in
/-- A Hilbert basis is infinite when the space admits a Hilbert basis indexed by the naturals. -/
theorem hilbertBasis_infinite_index {ι : Type*} (b : HilbertBasis ℕ ℂ H)
    (c : HilbertBasis ι ℂ H) : Infinite ι := by
  by_contra h
  have : Finite ι := not_infinite_iff_finite.mp h
  let : Fintype ι := Fintype.ofFinite ι
  have : Module.Finite ℂ H := Module.Finite.of_basis c.toOrthonormalBasis.toBasis
  have : Finite ℕ := b.orthonormal.linearIndependent.finite
  exact _root_.not_finite ℕ

/-- Compact symmetric Hilbert--Schmidt operators admit exactly the spectral data used in the paper. -/
theorem compact_symmetric_hilbertSchmidt_spectralData (T : H →L[ℂ] H)
    (hc : IsCompactOperator T) (hs : T.IsSymmetric) (hHS : IsHilbertSchmidt T) :
    Nonempty (SpectralData T) := by
  obtain ⟨b₀, hb₀⟩ := hHS
  obtain ⟨ι, b, μ, hd⟩ := compact_symmetric_exists_eigenbasis T hc hs
  have : Countable ι := hilbertBasis_countable_index b₀ b
  have : Infinite ι := hilbertBasis_infinite_index b₀ b
  let e : ℕ ≃ ι := Classical.choice inferInstance
  have hr : Set.range (b ∘ e) = Set.range b := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, congrArg b (e.apply_symm_apply i)⟩
  have hdense : ⊤ ≤ (Submodule.span ℂ (Set.range (b ∘ e))).topologicalClosure := by
    rw [hr, b.dense_span]
  let B : HilbertBasis ℕ ℂ H := HilbertBasis.mk (b.orthonormal.comp e e.injective) hdense
  have hB (j : ℕ) : B j = b (e j) := by
    exact congrFun (HilbertBasis.coe_mk _ hdense) j
  refine ⟨⟨B, μ ∘ e, ?_, ?_⟩⟩
  · intro j
    simpa only [hB, Function.comp_apply] using hd (e j)
  · have hsum := (hs_basis_independent T b₀ B hb₀).1
    have hn (j : ℕ) : ‖T (B j)‖ ^ 2 = (μ (e j)) ^ 2 := by
      rw [hB, hd, norm_smul, b.orthonormal.norm_eq_one, mul_one,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simpa only [hn, Function.comp_apply] using hsum

end ConditionalGoldbach
