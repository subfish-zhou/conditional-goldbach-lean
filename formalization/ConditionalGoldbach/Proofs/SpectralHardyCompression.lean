import ConditionalGoldbach.Proofs.SpectralBoundaryBlocks
import ConditionalGoldbach.Proofs.SpectralCompression
import ConditionalGoldbach.Proofs.HardyKernelOperator
import ConditionalGoldbach.Proofs.SpectralNormAttainment

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- The paper's Hardy compression preserves the exact HS norm once the boundary range is supported. -/
theorem hardyBoundaryCompression_hilbertSchmidt {a b : ℝ} (hab : a < b)
    (B : HardyBoundarySpace →L[ℂ] HardyBoundarySpace) (hB : B.IsSymmetric)
    (hR : ∀ f, B f ∈ Set.range (hardyTraceIsometry hab)) (hHS : IsHilbertSchmidt B)
    (c : HilbertBasis ℕ ℂ (HardySpace a b)) :
    IsHilbertSchmidt (hardyBoundaryCompression hab B) ∧
      hsNorm (hardyBoundaryCompression hab B) ^ 2 = hsNorm B ^ 2 :=
  isometricCompression_hilbertSchmidt (hardyTraceIsometry hab) B hB hR hHS c

/-- All operator-theoretic conclusions of Proposition 5.3 from the actual boundary realization. -/
theorem hardyBoundaryKernel_spectral_spec {a : ℝ} (ha : a < beta) (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hherm : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ), ∀ t u : ℝ,
      K (line y u) (line x t) = conj (K (line x t) (line y u)))
    (hR : ∀ f, boundaryKernelOperator a beta K hK f ∈ Set.range (hardyTraceIsometry ha))
    (b : HilbertBasis ℕ ℂ BoundaryL2) (c : HilbertBasis ℕ ℂ (HardySpace a beta)) :
    let T := hardyBoundaryCompression ha (boundaryKernelOperator a beta K hK)
    IsCompactOperator T ∧ IsSelfAdjoint T ∧ IsHilbertSchmidt T ∧ Nonempty (SpectralData T) ∧
      (∑' j, eigenvalues T j ^ 2) = hsNorm T ^ 2 ∧
      hsNorm T ^ 2 = BoundaryKernelSquareIntegral a beta K ∧
      ‖T‖ = sSup (Set.range (fun j => |eigenvalues T j|)) ∧
      (T ≠ 0 → ∃ j, |eigenvalues T j| = ‖T‖) := by
  let B := boundaryKernelOperator a beta K hK
  have hB : IsSelfAdjoint B := boundaryKernelOperator_isSelfAdjoint a beta K hK hherm
  have hBS := boundaryKernelOperator_hilbertSchmidt a beta ha.ne K hK b
  have hT := hardyBoundaryCompression_hilbertSchmidt ha B hB.isSymmetric hR hBS.1 c
  have hself := hardyBoundaryCompression_selfAdjoint ha hB
  have hspec := hT.1.spectralData hself.isSymmetric
  refine ⟨hT.1.isCompactOperator, hself, hT.1, hspec, ?_, hT.2.trans hBS.2,
    (spectral_norm_spec _ hspec).1, (spectral_norm_spec _ hspec).2⟩
  change (∑' j, eigenvalues (hardyBoundaryCompression ha B) j ^ 2) = _
  simpa only [eigenvalues, dite_eq_left hspec] using (Classical.choice hspec).hsNorm_sq.symm

end ConditionalGoldbach
