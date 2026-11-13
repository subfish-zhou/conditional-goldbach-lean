import LiLiuGoldbach.Proofs.SpectralHilbertSchmidtCompact

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Compression through a Hilbert-space isometry. -/
def isometricCompression (J : E →ₗᵢ[ℂ] H) (B : H →L[ℂ] H) : E →L[ℂ] E :=
  J.toContinuousLinearMap.adjoint ∘L B ∘L J.toContinuousLinearMap

/-- The adjoint projection fixes an operator whose range lies in the isometric image. -/
theorem isometricCompression_image (J : E →ₗᵢ[ℂ] H) (B : H →L[ℂ] H)
    (hR : ∀ x, B x ∈ Set.range J) (x : H) :
    J (J.toContinuousLinearMap.adjoint (B x)) = B x := by
  obtain ⟨y, hy⟩ := hR x
  have h := congrArg (fun T : E →L[ℂ] E => T y) J.adjoint_comp_self
  rw [← hy]
  change J (J.toContinuousLinearMap.adjoint (J y)) = J y
  exact congrArg J h

/-- Exact Hilbert--Schmidt preservation under compression when the whole range is supported there. -/
theorem isometricCompression_hilbertSchmidt (J : E →ₗᵢ[ℂ] H) (B : H →L[ℂ] H)
    (hB : B.IsSymmetric) (hR : ∀ x, B x ∈ Set.range J) (hHS : IsHilbertSchmidt B)
    (b : HilbertBasis ℕ ℂ E) :
    IsHilbertSchmidt (isometricCompression J B) ∧
      hsNorm (isometricCompression J B) ^ 2 = hsNorm B ^ 2 := by
  obtain ⟨c, hc⟩ := hHS
  let A := isometricCompression J B
  have himage := isometricCompression_image J B hR
  have hnorm (x : H) : ‖J.toContinuousLinearMap.adjoint (B x)‖ = ‖B x‖ := by
    rw [← J.norm_map, himage]
  have hnormA (x : E) : ‖A x‖ = ‖B (J x)‖ := hnorm (J x)
  let f : ℕ → ℕ → ℝ := fun i j => ‖inner ℂ (c j) (B (J (b i)))‖ ^ 2
  have hrow (i : ℕ) : HasSum (f i) (‖A (b i)‖ ^ 2) := by
    rw [hnormA]
    exact hilbertBasis_hasSum_sq_inner c (B (J (b i)))
  have hflip (i j : ℕ) : f i j = ‖inner ℂ (b i) (J.toContinuousLinearMap.adjoint (B (c j)))‖ ^ 2 := by
    dsimp [f]
    rw [← hB.apply_clm (c j) (J (b i))]
    nth_rw 1 [← himage (c j)]
    rw [J.inner_map_map, norm_inner_symm]
  have hcol (j : ℕ) : HasSum (fun i => f i j) (‖B (c j)‖ ^ 2) := by
    have hh := hilbertBasis_hasSum_sq_inner b (J.toContinuousLinearMap.adjoint (B (c j)))
    simpa only [← hflip, hnorm] using hh
  have hp' : Summable (fun p : ℕ × ℕ => f p.2 p.1) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
    refine ⟨fun j => (hcol j).summable, ?_⟩
    convert hc using 1
    funext j
    exact (hcol j).tsum_eq
  have hp : Summable (Function.uncurry f) := (Equiv.prodComm ℕ ℕ).summable_iff.mpr hp'
  have hA : Summable (fun i => ‖A (b i)‖ ^ 2) := by
    convert hp.prod using 1
    funext i
    exact (hrow i).tsum_eq.symm
  refine ⟨⟨b, hA⟩, ?_⟩
  rw [(proposition_5_3_hs_basis_independent _ ⟨b, hA⟩ b).2,
    (proposition_5_3_hs_basis_independent B ⟨c, hc⟩ c).2]
  calc
    (∑' i, ‖A (b i)‖ ^ 2) = ∑' i, ∑' j, f i j := by simp only [(hrow _).tsum_eq]
    _ = ∑' j, ∑' i, f i j := hp.tsum_comm.symm
    _ = ∑' j, ‖B (c j)‖ ^ 2 := by simp only [(hcol _).tsum_eq]

end LiLiuGoldbach16
