import LiLiuGoldbach.Proofs.HardyFiniteGram
import LiLiuGoldbach.Proofs.WeightedComponentKernel

/-! The arithmetic component is a finite positive Gram operator, with its exact boundary trace. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16

lemma arithmeticOperator_positive_trace_formula (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    IsPositiveTraceClass (arithmeticOperator ha N) ∧
      positiveTrace (arithmeticOperator ha N) =
        (2 / N.totient : ℝ) * ∑ χ ∈ oddCharacters N,
          ((∫ t : ℝ, ‖characterHardyFunction χ (line (alpha N) t)‖ ^ 2) +
            ∫ t : ℝ, ‖characterHardyFunction χ (line beta t)‖ ^ 2) := by
  classical
  let ι := {χ : Character N // χ ∈ oddCharacters N}
  have hgex (χ : ι) := characterHardyFunction_representation N hlarge hGRH ha χ.val χ.property
  choose g hg hgl hgr using hgex
  let c : ℝ := 2 / N.totient
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let v : ι → HardySpace (alpha N) beta := fun χ => (Real.sqrt c : ℂ) • g χ
  let f : ι → ℂ → ℂ := fun χ s => (Real.sqrt c : ℂ) * characterHardyFunction χ.val s
  have hvf (χ : ι) (s : ℂ) (hs : s ∈ strip (alpha N) beta) : fourierLaplace (v χ) s = f χ s := by
    dsimp only [v]
    rw [fourierLaplace_smul _ _ hs, hg χ s hs]
  have hvl (χ : ι) : (boundaryTraces ha (v χ)).1 =ᵐ[volume] fun t => f χ (line (alpha N) t) := by
    dsimp only [v]
    rw [boundaryTraces_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt c : ℂ) (boundaryTraces ha (g χ)).1, hgl χ] with t ht hg
    change ((Real.sqrt c : ℂ) • (boundaryTraces ha (g χ)).1) t = _
    rw [ht, Pi.smul_apply, smul_eq_mul, hg]
  have hvr (χ : ι) : (boundaryTraces ha (v χ)).2 =ᵐ[volume] fun t => f χ (line beta t) := by
    dsimp only [v]
    rw [boundaryTraces_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt c : ℂ) (boundaryTraces ha (g χ)).2, hgr χ] with t ht hg
    change ((Real.sqrt c : ℂ) • (boundaryTraces ha (g χ)).2) t = _
    rw [ht, Pi.smul_apply, smul_eq_mul, hg]
  have hc_cast : (c : ℂ) = (2 : ℂ) / N.totient := by dsimp [c]; push_cast; rfl
  have hc_sq : (Real.sqrt c : ℂ) ^ 2 = (c : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hc]
  have hgram (s z : ℂ) : weightedAnalyticKernel (characterKernel N) s z = ∑ χ : ι, f χ s * conj (f χ z) := by
    dsimp only [f, weightedAnalyticKernel, characterHardyFunction]
    rw [Finset.sum_coe_sort (oddCharacters N) (fun χ : Character N =>
      (Real.sqrt c : ℂ) * (logDerivative χ s / (1 + s)) *
        conj ((Real.sqrt c : ℂ) * (logDerivative χ z / (1 + z))))]
    simp only [characterKernel, Complex.conj_conj]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [map_mul, Complex.conj_ofReal, map_div₀, map_add, map_one]
    calc
      (2 / (N.totient : ℂ) * (logDerivative χ s * conj (logDerivative χ z))) /
          ((1 + s) * (1 + conj z)) =
        (Real.sqrt c : ℂ) ^ 2 * (logDerivative χ s / (1 + s)) *
          (conj (logDerivative χ z) / (1 + conj z)) := by
          rw [hc_sq, hc_cast]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
      _ = _ := by ring
  have hrep := hardyFiniteGram_represents ha N v f (weightedAnalyticKernel (characterKernel N)) hvf hvl hvr hgram
  have he : arithmeticOperator ha N = ∑ χ : ι, rankOne ℂ (v χ) (v χ) :=
    kernelOperator_eq_of_represents ha N hrep
  have ht := rankOne_tsum_positiveTraceClass v (hasSum_fintype (fun χ : ι => ‖v χ‖ ^ 2)).summable
    (Classical.choice (hardySpace_exists_nat_hilbertBasis (alpha N) beta))
  rw [tsum_fintype, tsum_fintype] at ht
  refine ⟨he ▸ ht.1, ?_⟩
  rw [he, ht.2]
  have hnorm (χ : ι) : ‖v χ‖ ^ 2 = c *
      ((∫ t : ℝ, ‖characterHardyFunction χ.val (line (alpha N) t)‖ ^ 2) +
        ∫ t : ℝ, ‖characterHardyFunction χ.val (line beta t)‖ ^ 2) := by
    dsimp only [v]
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hc, boundaryTraces_norm_sq ha (g χ),
      l2_norm_sq_integral, l2_norm_sq_integral]
    congr 1
    apply congrArg₂ (· + ·)
    · exact integral_congr_ae ((hgl χ).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    · exact integral_congr_ae ((hgr χ).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  simp_rw [hnorm]
  rw [← Finset.mul_sum, Finset.sum_coe_sort (oddCharacters N) (fun χ : Character N =>
    (∫ t : ℝ, ‖characterHardyFunction χ (line (alpha N) t)‖ ^ 2) +
      ∫ t : ℝ, ‖characterHardyFunction χ (line beta t)‖ ^ 2)]

end LiLiuGoldbach16
