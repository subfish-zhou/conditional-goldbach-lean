import ConditionalGoldbach.Proofs.SpectralHilbertSchmidt
import ConditionalGoldbach.Proofs.SpectralPositiveTrace
import ConditionalGoldbach.Proofs.SpectralBasisExistence

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator norm is bounded by the square root of its Hilbert--Schmidt square sum. -/
theorem hilbertSchmidt_norm_le (T : H →L[ℂ] H) (b : HilbertBasis ℕ ℂ H)
    (hb : Summable (fun j => ‖T (b j)‖ ^ 2)) :
    ‖T‖ ≤ Real.sqrt (∑' j, ‖T (b j)‖ ^ 2) := by
  obtain ⟨hb', heq⟩ := hs_adjoint_basis_relation T b b hb
  have hn : 0 ≤ ∑' j, ‖T (b j)‖ ^ 2 := tsum_nonneg (fun j => sq_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hsx := hilbertBasis_hasSum_sq_inner b (T x)
  have hsq : ‖T x‖ ^ 2 ≤ (∑' j, ‖T (b j)‖ ^ 2) * ‖x‖ ^ 2 := by
    rw [← hsx.tsum_eq, heq, ← tsum_mul_right]
    apply Summable.tsum_le_tsum ?_ hsx.summable (hb'.mul_right (‖x‖ ^ 2))
    intro j
    rw [← ContinuousLinearMap.adjoint_inner_left]
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) ((ContinuousLinearMap.adjoint T) (b j)) x) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hn] using hsq

/-- Finite basis truncations of a Hilbert--Schmidt operator converge in operator norm. -/
theorem hilbertSchmidt_tendsto_finiteRank (T : H →L[ℂ] H) (b : HilbertBasis ℕ ℂ H)
    (hb : Summable (fun j => ‖T (b j)‖ ^ 2)) :
    Tendsto (fun s : Finset ℕ => ∑ j ∈ s, rankOne ℂ (T (b j)) (b j)) atTop (𝓝 T) := by
  let F : Finset ℕ → H →L[ℂ] H := fun s => ∑ j ∈ s, rankOne ℂ (T (b j)) (b j)
  have hF (s : Finset ℕ) (k : ℕ) : F s (b k) = if k ∈ s then T (b k) else 0 := by
    dsimp [F]
    simp only [sum_apply, rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal, ite_smul, one_smul, zero_smul]
    exact Finset.sum_ite_eq' s k (fun j => T (b j))
  have herr (s : Finset ℕ) (k : ℕ) :
      ‖(T - F s) (b k)‖ ^ 2 = if k ∈ s then 0 else ‖T (b k)‖ ^ 2 := by
    rw [sub_apply, hF]
    split_ifs <;> simp
  have hsum (s : Finset ℕ) : Summable (fun j => ‖(T - F s) (b j)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) ?_ hb
    intro j
    rw [herr]
    split_ifs
    · positivity
    · exact le_rfl
  have htsum (s : Finset ℕ) : (∑' j, ‖(T - F s) (b j)‖ ^ 2) =
      ∑' j : {k // k ∉ s}, ‖T (b j)‖ ^ 2 := by
    calc
      (∑' j, ‖(T - F s) (b j)‖ ^ 2) =
          ∑' j, ({k : ℕ | k ∉ s} : Set ℕ).indicator (fun j => ‖T (b j)‖ ^ 2) j := by
        apply tsum_congr
        intro j
        rw [herr]
        simp only [Set.indicator, Set.mem_ofPred_eq]
        split_ifs <;> simp_all
      _ = _ := (tsum_subtype ({k : ℕ | k ∉ s} : Set ℕ) (fun j => ‖T (b j)‖ ^ 2)).symm
  have htail : Tendsto (fun s : Finset ℕ => Real.sqrt (∑' j, ‖(T - F s) (b j)‖ ^ 2))
      atTop (𝓝 0) := by
    simp only [htsum]
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_tsum_compl_atTop_zero (fun j => ‖T (b j)‖ ^ 2))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _) ?_ htail
  apply Filter.Eventually.of_forall
  intro s
  rw [norm_sub_rev]
  exact hilbertSchmidt_norm_le (T - F s) b (hsum s)

/-- Every Hilbert--Schmidt operator in the paper's sense is compact. -/
theorem IsHilbertSchmidt.isCompactOperator {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  obtain ⟨b, hb⟩ := hT
  apply isCompactOperator_of_tendsto (hilbertSchmidt_tendsto_finiteRank T b hb)
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, FunLike.coe_zero] using
      (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj, FunLike.coe_add] using
      (rankOne_isCompactOperator (T (b j)) (b j)).add ih

/-- Symmetry and the paper's Hilbert--Schmidt condition suffice for spectral data. -/
theorem IsHilbertSchmidt.spectralData {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (hs : T.IsSymmetric) : Nonempty (SpectralData T) :=
  compact_symmetric_hilbertSchmidt_spectralData T hT.isCompactOperator hs hT

end ConditionalGoldbach
