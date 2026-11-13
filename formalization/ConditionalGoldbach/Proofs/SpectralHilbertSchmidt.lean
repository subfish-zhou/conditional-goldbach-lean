import ConditionalGoldbach.Proofs.SpectralCompletionTrace

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Double Parseval identifies Hilbert--Schmidt sums for an operator and its adjoint. -/
theorem hs_adjoint_basis_relation (T : H →L[ℂ] H)
    (b c : HilbertBasis ℕ ℂ H) (hb : Summable (fun j => ‖T (b j)‖ ^ 2)) :
    Summable (fun j => ‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2) ∧
      (∑' j, ‖T (b j)‖ ^ 2) = ∑' j, ‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2 := by
  let f : ℕ → ℕ → ℝ := fun i j => ‖inner ℂ (c j) (T (b i))‖ ^ 2
  have hrow (i : ℕ) : HasSum (f i) (‖T (b i)‖ ^ 2) :=
    hilbertBasis_hasSum_sq_inner c (T (b i))
  have hflip (i j : ℕ) : f i j = ‖inner ℂ (b i) ((ContinuousLinearMap.adjoint T) (c j))‖ ^ 2 := by
    dsimp [f]
    rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
  have hcol (j : ℕ) : HasSum (fun i => f i j) (‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2) := by
    simpa only [hflip] using hilbertBasis_hasSum_sq_inner b ((ContinuousLinearMap.adjoint T) (c j))
  have hp : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).2
    refine ⟨fun i => (hrow i).summable, ?_⟩
    convert hb using 1
    funext i
    exact (hrow i).tsum_eq
  have hp' : Summable (fun p : ℕ × ℕ => f p.2 p.1) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.2 hp
  refine ⟨?_, ?_⟩
  · convert hp'.prod using 1
    funext j
    exact (hcol j).tsum_eq.symm
  · calc
      (∑' j, ‖T (b j)‖ ^ 2) = ∑' i, ∑' j, f i j := by simp only [(hrow _).tsum_eq]
      _ = ∑' j, ∑' i, f i j := hp.tsum_comm.symm
      _ = ∑' j, ‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2 := by simp only [(hcol _).tsum_eq]

/-- The Hilbert--Schmidt sum is independent of the basis for an arbitrary operator. -/
theorem hs_basis_independent (T : H →L[ℂ] H) (b c : HilbertBasis ℕ ℂ H)
    (hb : Summable (fun j => ‖T (b j)‖ ^ 2)) :
    Summable (fun j => ‖T (c j)‖ ^ 2) ∧
      (∑' j, ‖T (b j)‖ ^ 2) = ∑' j, ‖T (c j)‖ ^ 2 := by
  obtain ⟨h₁, he₁⟩ := hs_adjoint_basis_relation T b b hb
  obtain ⟨h₂, he₂⟩ := hs_adjoint_basis_relation (ContinuousLinearMap.adjoint T) b c h₁
  simp only [ContinuousLinearMap.adjoint_adjoint] at h₂ he₂
  exact ⟨h₂, he₁.trans he₂⟩

/-- The reviewed paper statement, including the original choice-based Hilbert--Schmidt norm. -/
theorem proposition_5_3_hs_basis_independent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : IsHilbertSchmidt T) (b : HilbertBasis ℕ ℂ H) :
    Summable (fun j => ‖T (b j)‖ ^ 2) ∧
    hsNorm T ^ 2 = ∑' j, ‖T (b j)‖ ^ 2 := by
  unfold IsHilbertSchmidt at hT
  have hb := hs_basis_independent T (Classical.choose hT) b (Classical.choose_spec hT)
  refine ⟨hb.1, ?_⟩
  unfold hsNorm
  rw [dite_eq_left hT, Real.sq_sqrt (tsum_nonneg fun j => sq_nonneg _)]
  exact hb.2

end ConditionalGoldbach
