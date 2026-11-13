import ConditionalGoldbach.Proofs.SpectralRankOneSeries
import ConditionalGoldbach.Proofs.HardyEvaluation
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- Absolute convergence in a Hilbert space gives pointwise almost-everywhere convergence after an L²-valued bounded map. -/
theorem clm_l2_hasSum_ae {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (L : H →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) (v : ℕ → H)
    (hv : Summable (fun j => ‖v j‖)) :
    ∀ᵐ t : ℝ, HasSum (fun j => L (v j) t) (L (∑' j, v j) t) := by
  have hs : Summable (fun j => ‖L (v j)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => L.le_opNorm (v j))
      (hv.mul_left ‖L‖)
  have heq := (L.hasSum (Summable.of_norm hv).hasSum).tsum_eq
  rw [← heq]
  exact Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hs)

/-- The two Hardy traces preserve absolutely convergent series pointwise almost everywhere. -/
theorem hardyTrace_hasSum_ae {a b : ℝ} (hab : a < b) (v : ℕ → HardySpace a b)
    (hv : Summable (fun j => ‖v j‖)) :
    (∀ᵐ t : ℝ, HasSum (fun j => (boundaryTraces hab (v j)).1 t)
      ((boundaryTraces hab (∑' j, v j)).1 t)) ∧
    (∀ᵐ t : ℝ, HasSum (fun j => (boundaryTraces hab (v j)).2 t)
      ((boundaryTraces hab (∑' j, v j)).2 t)) := by
  let J := (hardyTraceIsometry hab).toContinuousLinearMap
  let L := (WithLp.fstL 2 ℂ (Lp ℂ 2 (volume : Measure ℝ)) (Lp ℂ 2 (volume : Measure ℝ))).comp J
  let R := (WithLp.sndL 2 ℂ (Lp ℂ 2 (volume : Measure ℝ)) (Lp ℂ 2 (volume : Measure ℝ))).comp J
  exact ⟨clm_l2_hasSum_ae L v hv, clm_l2_hasSum_ae R v hv⟩

/-- Positive rank-one Hardy series realize their actual pointwise boundary kernels. -/
theorem hardyRankOneSeries_represents {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (v : ℕ → HardySpace a beta) (f : ℕ → ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (hv : Summable (fun j => ‖v j‖ ^ 2))
    (hf : ∀ j s, s ∈ strip a beta → fourierLaplace (v j) s = f j s)
    (hl : ∀ j, (boundaryTraces ha (v j)).1 =ᵐ[volume] fun t => f j (line a t))
    (hr : ∀ j, (boundaryTraces ha (v j)).2 =ᵐ[volume] fun t => f j (line beta t))
    (hKl : ∀ s ∈ strip a beta, ∀ t, K s (line a t) = ∑' j, f j s * conj (f j (line a t)))
    (hKr : ∀ s ∈ strip a beta, ∀ t, K s (line beta t) = ∑' j, f j s * conj (f j (line beta t))) :
    RepresentsKernel ha N K (∑' j, rankOne ℂ (v j) (v j)) := by
  intro ψ s hs
  let u : ℕ → HardySpace a beta := fun j => conj (f j s) • v j
  let w : HardySpace a beta := ∑' j, u j
  have hu : Summable (fun j => ‖u j‖) := by
    apply (hv.mul_left ‖(evaluationVector s : HardySpace a beta)‖).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    intro j
    dsimp only [u]
    rw [norm_smul, norm_conj]
    have he := norm_fourierLaplace_le hs (v j)
    rw [hf j s hs] at he
    nlinarith [norm_nonneg (v j)]
  have hsum := (Summable.of_norm hu).hasSum
  have hpair := ((innerSL ℂ ψ).hasSum hsum).star
  have hpair' : HasSum (fun j => inner ℂ (v j) ψ * f j s) (paperInner ψ w) := by
    convert hpair using 1
    · funext j
      change inner ℂ (v j) ψ * f j s = conj (inner ℂ ψ (conj (f j s) • v j))
      rw [inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm, mul_comm]
    · change inner ℂ w ψ = conj (inner ℂ ψ w)
      exact (inner_conj_symm w ψ).symm
  have heval := (hardyEvaluationFunctional s).hasSum
    ((ContinuousLinearMap.apply ℂ (HardySpace a beta) ψ).hasSum (summable_rankOne_self v hv).hasSum)
  have heval' : HasSum (fun j => inner ℂ (v j) ψ * f j s)
      (fourierLaplace ((∑' j, rankOne ℂ (v j) (v j)) ψ) s) := by
    simpa only [ContinuousLinearMap.apply_apply, rankOne_apply, map_smul, smul_eq_mul,
      hardyEvaluationFunctional_apply hs, fourierLaplace_smul _ _ hs, hf _ s hs] using heval
  rw [heval'.unique hpair', lemma_5_2_boundary_inner a beta ha ψ w]
  have htr := hardyTrace_hasSum_ae ha u hu
  have hleft : (fun t => conj ((boundaryTraces ha w).1 t)) =ᵐ[volume] fun t => K s (line a t) := by
    filter_upwards [htr.1, ae_all_iff.mpr hl,
      ae_all_iff.mpr (fun j => Lp.coeFn_smul (conj (f j s)) (boundaryTraces ha (v j)).1)] with t ht htf hsm
    have ht' := ht.star
    change HasSum (fun j => conj ((boundaryTraces ha (u j)).1 t))
      (conj ((boundaryTraces ha w).1 t)) at ht'
    have hterms (j : ℕ) : conj ((boundaryTraces ha (u j)).1 t) = f j s * conj (f j (line a t)) := by
      rw [show u j = conj (f j s) • v j from rfl, boundaryTraces_smul]
      change conj (((conj (f j s)) • (boundaryTraces ha (v j)).1) t) = _
      rw [hsm j, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj, htf j]
    rw [hKl s hs t, ← ht'.tsum_eq]
    exact tsum_congr hterms
  have hright : (fun t => conj ((boundaryTraces ha w).2 t)) =ᵐ[volume] fun t => K s (line beta t) := by
    filter_upwards [htr.2, ae_all_iff.mpr hr,
      ae_all_iff.mpr (fun j => Lp.coeFn_smul (conj (f j s)) (boundaryTraces ha (v j)).2)] with t ht htf hsm
    have ht' := ht.star
    change HasSum (fun j => conj ((boundaryTraces ha (u j)).2 t))
      (conj ((boundaryTraces ha w).2 t)) at ht'
    have hterms (j : ℕ) : conj ((boundaryTraces ha (u j)).2 t) = f j s * conj (f j (line beta t)) := by
      rw [show u j = conj (f j s) • v j from rfl, boundaryTraces_smul]
      change conj (((conj (f j s)) • (boundaryTraces ha (v j)).2) t) = _
      rw [hsm j, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj, htf j]
    rw [hKr s hs t, ← ht'.tsum_eq]
    exact tsum_congr hterms
  unfold kernelAction
  congr 1
  · apply integral_congr_ae
    filter_upwards [hleft] with t ht
    rw [ht, mul_comm]
  · apply integral_congr_ae
    filter_upwards [hright] with t ht
    rw [ht, mul_comm]

end ConditionalGoldbach
