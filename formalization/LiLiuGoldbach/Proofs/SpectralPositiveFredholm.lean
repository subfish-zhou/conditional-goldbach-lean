import LiLiuGoldbach.Proofs.SpectralBasisExistence

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positive trace-class operators have genuine countable spectral data. -/
theorem IsPositiveTraceClass.spectralData {A : H →L[ℂ] H} (hA : IsPositiveTraceClass A) :
    Nonempty (SpectralData A) :=
  compact_symmetric_hilbertSchmidt_spectralData A hA.isCompactOperator hA.1 hA.isHilbertSchmidt

/-- The complete reviewed positive Fredholm specification. -/
theorem proposition_6_1_positive_fredholm_spec {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H)
    (hA : IsPositiveTraceClass A) :
    IsCompactOperator A ∧ IsHilbertSchmidt A ∧ Nonempty (SpectralData A) ∧
    (∀ j, 0 ≤ eigenvalues A j) ∧ Summable (eigenvalues A) ∧
    positiveTrace A = ∑' j, eigenvalues A j ∧
    (∀ b : HilbertBasis ℕ ℂ H,
      Summable (fun j => (paperInner (A (b j)) (b j)).re) ∧
      positiveTrace A = ∑' j, (paperInner (A (b j)) (b j)).re) ∧
    (∀ t : ℂ, Multipliable (fun j : ℕ => 1 - t * (eigenvalues A j : ℂ))) := by
  have hdata := hA.spectralData
  let d := Classical.choice hdata
  have heig : eigenvalues A = d.values := by simp only [eigenvalues, dite_eq_left hdata, d]
  have hquad (j : ℕ) : (paperInner (A (d.basis j)) (d.basis j)).re = d.values j := by
    change (inner ℂ (d.basis j) (A (d.basis j))).re = _
    rw [d.diagonal, inner_smul_right, inner_self_eq_norm_sq_to_K,
      d.basis.orthonormal.norm_eq_one]
    simp
  have htrace := hA.trace_basis_independent d.basis
  simp only [hquad] at htrace
  refine ⟨hA.isCompactOperator, hA.isHilbertSchmidt, hdata, ?_, ?_, ?_,
    hA.trace_basis_independent, ?_⟩
  · intro j
    rw [heig, ← hquad]
    exact hA.2.1 (d.basis j)
  · simpa only [heig] using htrace.1
  · simpa only [heig] using htrace.2
  · intro t
    have hs : Summable (fun j => -(t * (d.values j : ℂ))) :=
      ((Complex.summable_ofReal.mpr htrace.1).mul_left t).neg
    simpa only [heig, sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs

end LiLiuGoldbach16
