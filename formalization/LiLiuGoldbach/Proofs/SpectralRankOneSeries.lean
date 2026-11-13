import LiLiuGoldbach.Proofs.SpectralPositiveTrace

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Absolute convergence of positive rank-one expansions. -/
theorem summable_rankOne_self {ι : Type*} (v : ι → H) (hv : Summable (fun j => ‖v j‖ ^ 2)) :
    Summable (fun j => rankOne ℂ (v j) (v j)) :=
  hv.of_norm_bounded fun j => by simp only [norm_rankOne, pow_two, le_refl]

/-- A convergent sum of positive rank-one maps is self-adjoint. -/
theorem rankOne_tsum_selfAdjoint {ι : Type*} (v : ι → H) :
    IsSelfAdjoint (∑' j, rankOne ℂ (v j) (v j)) := by
  change star (∑' j, rankOne ℂ (v j) (v j)) = _
  simp only [tsum_star, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- The quadratic form of a positive rank-one series is a sum of squared scalar products. -/
theorem rankOne_tsum_quadratic_hasSum {ι : Type*} (v : ι → H)
    (hv : Summable (fun j => ‖v j‖ ^ 2)) (x : H) :
    HasSum (fun j => ‖inner ℂ (v j) x‖ ^ 2)
      (paperInner ((∑' j, rankOne ℂ (v j) (v j)) x) x).re := by
  have hs := Complex.hasSum_re ((innerSL ℂ x).hasSum
    ((ContinuousLinearMap.apply ℂ H x).hasSum (summable_rankOne_self v hv).hasSum))
  convert hs using 1
  · funext j
    simp only [ContinuousLinearMap.apply_apply, innerSL_apply_apply, rankOne_apply, inner_smul_right]
    rw [← inner_conj_symm x (v j), Complex.mul_conj, ofReal_re, Complex.normSq_eq_norm_sq]
  · rfl

/-- A square-summable vector family defines a positive trace-class operator, with its exact trace. -/
theorem rankOne_tsum_positiveTraceClass {ι : Type*} (v : ι → H)
    (hv : Summable (fun j => ‖v j‖ ^ 2)) (b : HilbertBasis ℕ ℂ H) :
    IsPositiveTraceClass (∑' j, rankOne ℂ (v j) (v j)) ∧
      positiveTrace (∑' j, rankOne ℂ (v j) (v j)) = ∑' j, ‖v j‖ ^ 2 := by
  let f : ι → ℕ → ℝ := fun j k => ‖inner ℂ (v j) (b k)‖ ^ 2
  have hrow (j : ι) : HasSum (f j) (‖v j‖ ^ 2) := by
    simpa only [f, norm_inner_symm] using hilbertBasis_hasSum_sq_inner b (v j)
  have hp : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun j => (hrow j).summable, ?_⟩
    convert hv using 1
    funext j
    exact (hrow j).tsum_eq
  have hcol (k : ℕ) := rankOne_tsum_quadratic_hasSum v hv (b k)
  have hb : Summable (fun k => (paperInner ((∑' j, rankOne ℂ (v j) (v j)) (b k)) (b k)).re) := by
    have hs := ((Equiv.prodComm ℕ ι).summable_iff.mpr hp).prod
    convert hs using 1
    funext k
    exact (hcol k).tsum_eq.symm
  have hT : IsPositiveTraceClass (∑' j, rankOne ℂ (v j) (v j)) := by
    refine ⟨(rankOne_tsum_selfAdjoint v).isSymmetric, ?_, ⟨b, hb⟩⟩
    intro x
    rw [← (rankOne_tsum_quadratic_hasSum v hv x).tsum_eq]
    exact tsum_nonneg (fun _ => sq_nonneg _)
  refine ⟨hT, (hT.trace_basis_independent b).2.trans ?_⟩
  calc
    _ = ∑' k, ∑' j, f j k := by
      apply tsum_congr
      intro k
      exact (hcol k).tsum_eq.symm
    _ = ∑' j, ∑' k, f j k := hp.tsum_comm
    _ = _ := by simp only [(hrow _).tsum_eq]

end LiLiuGoldbach16
