import LiLiuGoldbach.Proofs.CharacterHardyVectors

/-! Finite Gram kernels are represented by finite sums of positive rank-one maps. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16

lemma hardyFiniteGram_represents {ι : Type*} [Fintype ι] {a : ℝ} (ha : a < beta)
    (N : ℕ) [NeZero N] (v : ι → HardySpace a beta) (f : ι → ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (hf : ∀ j s, s ∈ strip a beta → fourierLaplace (v j) s = f j s)
    (hl : ∀ j, (boundaryTraces ha (v j)).1 =ᵐ[volume] fun t => f j (line a t))
    (hr : ∀ j, (boundaryTraces ha (v j)).2 =ᵐ[volume] fun t => f j (line beta t))
    (hK : ∀ s z, K s z = ∑ j, f j s * conj (f j z)) :
    RepresentsKernel ha N K (∑ j, rankOne ℂ (v j) (v j)) := by
  classical
  intro h s hs
  have hIl (j : ι) : Integrable (fun t : ℝ => f j s *
      ((boundaryTraces ha h).1 t * conj ((boundaryTraces ha (v j)).1 t))) := by
    simpa only [RCLike.inner_apply] using
      (L2.integrable_inner (𝕜 := ℂ) (boundaryTraces ha (v j)).1 (boundaryTraces ha h).1).const_mul (f j s)
  have hIr (j : ι) : Integrable (fun t : ℝ => f j s *
      ((boundaryTraces ha h).2 t * conj ((boundaryTraces ha (v j)).2 t))) := by
    simpa only [RCLike.inner_apply] using
      (L2.integrable_inner (𝕜 := ℂ) (boundaryTraces ha (v j)).2 (boundaryTraces ha h).2).const_mul (f j s)
  have heL : (fun t : ℝ => K s (line a t) * (boundaryTraces ha h).1 t) =ᵐ[volume]
      (fun t => ∑ j, f j s * ((boundaryTraces ha h).1 t * conj ((boundaryTraces ha (v j)).1 t))) := by
    filter_upwards [ae_all_iff.mpr hl] with t ht
    rw [hK, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [ht j]
    ring
  have heR : (fun t : ℝ => K s (line beta t) * (boundaryTraces ha h).2 t) =ᵐ[volume]
      (fun t => ∑ j, f j s * ((boundaryTraces ha h).2 t * conj ((boundaryTraces ha (v j)).2 t))) := by
    filter_upwards [ae_all_iff.mpr hr] with t ht
    rw [hK, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [ht j]
    ring
  rw [← hardyEvaluationFunctional_apply hs, ContinuousLinearMap.sum_apply, map_sum]
  simp only [rankOne_apply, map_smul, smul_eq_mul, hardyEvaluationFunctional_apply hs, hf _ s hs]
  unfold kernelAction
  rw [integral_congr_ae heL, integral_congr_ae heR,
    integral_finset_sum _ (fun j _ => hIl j), integral_finset_sum _ (fun j _ => hIr j),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_const_mul, ← mul_add,
    ← lemma_5_2_boundary_inner a beta ha h (v j)]
  rw [fourierLaplace_smul _ _ hs, hf j s hs]
  exact mul_comm _ _

end LiLiuGoldbach16
