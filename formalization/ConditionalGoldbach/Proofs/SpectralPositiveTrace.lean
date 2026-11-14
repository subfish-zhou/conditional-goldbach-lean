module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import ConditionalGoldbach.Proofs.SpectralCompletionTrace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The paper's positive trace-class predicate implies operator positivity. -/
theorem IsPositiveTraceClass.isPositive {A : H →L[ℂ] H} (hA : IsPositiveTraceClass A) :
    A.IsPositive := by
  refine ⟨hA.1, fun x => ?_⟩
  change 0 ≤ (inner ℂ (A x) x).re
  rw [hA.1.apply_clm x x]
  exact hA.2.1 x

/-- A positive trace-class operator is the square of a symmetric Hilbert--Schmidt operator. -/
theorem IsPositiveTraceClass.exists_hilbertSchmidt_square {A : H →L[ℂ] H}
    (hA : IsPositiveTraceClass A) :
    ∃ S : H →L[ℂ] H, S.IsSymmetric ∧ IsHilbertSchmidt S ∧ S.comp S = A := by
  let S : H →L[ℂ] H := CFC.sqrt A
  have hS : S.IsSymmetric :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)).isSymmetric
  have hsq : S.comp S = A := CFC.sqrt_mul_sqrt_self A
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA.isPositive)
  refine ⟨S, hS, ?_, hsq⟩
  obtain ⟨b, hb⟩ := hA.2.2
  refine ⟨b, ?_⟩
  have hquad (x : H) : (paperInner (A x) x).re = ‖S x‖ ^ 2 := by
    rw [← hsq]
    change (inner ℂ x (S (S x))).re = _
    rw [← hS.apply_clm x (S x)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (S x)
  simpa only [hquad] using hb

/-- Positivity and summable diagonal entries imply Hilbert--Schmidt summability. -/
theorem IsPositiveTraceClass.isHilbertSchmidt {A : H →L[ℂ] H}
    (hA : IsPositiveTraceClass A) : IsHilbertSchmidt A := by
  obtain ⟨S, hS, ⟨b, hb⟩, rfl⟩ := hA.exists_hilbertSchmidt_square
  refine ⟨b, Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
    (hb.mul_left (‖S‖ ^ 2))⟩
  change ‖S (S (b j))‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖S (b j)‖ ^ 2
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm (S (b j))) 2

/-- The original trace is independent of the arbitrary Hilbert-basis choice. -/
theorem IsPositiveTraceClass.trace_basis_independent {A : H →L[ℂ] H}
    (hA : IsPositiveTraceClass A) (b : HilbertBasis ℕ ℂ H) :
    Summable (fun j => (paperInner (A (b j)) (b j)).re) ∧
      positiveTrace A = ∑' j, (paperInner (A (b j)) (b j)).re := by
  obtain ⟨S, hS, hHS, rfl⟩ := hA.exists_hilbertSchmidt_square
  have hquad (x : H) : (paperInner ((S.comp S) x) x).re = ‖S x‖ ^ 2 := by
    change (inner ℂ x (S (S x))).re = _
    rw [← hS.apply_clm x (S x)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (S x)
  have hb : Summable (fun j => ‖S (b j)‖ ^ 2) := by
    obtain ⟨c, hc⟩ := hHS
    exact (symmetric_hs_basis_independent S hS c b hc).1
  refine ⟨by simpa only [hquad] using hb, ?_⟩
  rw [symmetric_square_trace_eq_hsNorm S hS hHS]
  unfold IsHilbertSchmidt at hHS
  unfold hsNorm
  rw [dite_eq_left hHS, Real.sq_sqrt (tsum_nonneg fun j => sq_nonneg _)]
  simp only [hquad]
  exact (symmetric_hs_basis_independent S hS _ b (Classical.choose_spec hHS)).2

/-- A symmetric Hilbert--Schmidt square is an absolutely convergent sum of rank-one maps. -/
theorem symmetric_hs_square_hasSum_rankOne (S : H →L[ℂ] H) (hS : S.IsSymmetric)
    (b : HilbertBasis ℕ ℂ H) (hb : Summable (fun j => ‖S (b j)‖ ^ 2)) :
    HasSum (fun j => rankOne ℂ (S (b j)) (S (b j))) (S.comp S) := by
  have hs : Summable (fun j => rankOne ℂ (S (b j)) (S (b j))) :=
    hb.of_norm_bounded fun j => by simp only [norm_rankOne, pow_two, le_refl]
  suffices heq : (∑' j, rankOne ℂ (S (b j)) (S (b j))) = S.comp S by
    exact heq ▸ hs.hasSum
  ext x
  have h₁ := (ContinuousLinearMap.apply ℂ H x).hasSum hs.hasSum
  have h₂ := S.hasSum (b.hasSum_repr (S x))
  apply h₁.unique
  convert h₂ using 1
  · funext j
    simp only [ContinuousLinearMap.apply_apply, rankOne_apply, HilbertBasis.repr_apply_apply,
      map_smul, hS.apply_clm]
  · rfl

omit [CompleteSpace H] in
/-- Rank-one operators are compact, by their factorization through the scalar field. -/
theorem rankOne_isCompactOperator (x y : H) : IsCompactOperator (rankOne ℂ x y) := by
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)

/-- A positive trace-class operator is compact, using its convergent rank-one expansion. -/
theorem IsPositiveTraceClass.isCompactOperator {A : H →L[ℂ] H}
    (hA : IsPositiveTraceClass A) : IsCompactOperator A := by
  obtain ⟨S, hS, ⟨b, hb⟩, rfl⟩ := hA.exists_hilbertSchmidt_square
  apply isCompactOperator_of_tendsto (symmetric_hs_square_hasSum_rankOne S hS b hb)
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, FunLike.coe_zero] using
      (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj, FunLike.coe_add] using
      (rankOne_isCompactOperator (S (b j)) (S (b j))).add ih

end ConditionalGoldbach
