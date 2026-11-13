import ConditionalGoldbach.Proofs.HardyEvaluation
import Mathlib.Analysis.Normed.Module.WeakDual

/-! Weak compactness closes uniformly bounded Fourier–Laplace families under pointwise limits. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma hardy_bounded_pointwise_limit {a b C : ℝ} (ψ : ℕ → HardySpace a b)
    (hbound : ∀ n, ‖ψ n‖ ≤ C) (f : ℂ → ℂ)
    (hlim : ∀ s ∈ strip a b, Tendsto (fun n => fourierLaplace (ψ n) s) atTop (𝓝 (f s))) :
    ∃ χ : HardySpace a b, ‖χ‖ ≤ C ∧ ∀ s ∈ strip a b, fourierLaplace χ s = f s := by
  let u : ℕ → WeakDual ℂ (HardySpace a b) := fun n =>
    (InnerProductSpace.toDual ℂ (HardySpace a b) (ψ n)).toWeakDual
  have hc := WeakDual.isCompact_closedBall (0 : StrongDual ℂ (HardySpace a b)) C
  have hu : Filter.map u atTop ≤ 𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C) := by
    apply le_principal_iff.mpr
    change ∀ᶠ n : ℕ in atTop, (u n).toStrongDual ∈ Metric.closedBall 0 C
    filter_upwards [] with n
    simpa only [u, StrongDual.toStrongDual_toWeakDual, Metric.mem_closedBall,
      dist_zero_right, LinearIsometryEquiv.norm_map] using hbound n
  obtain ⟨v, hv, hcluster⟩ := hc.exists_mapClusterPt hu
  let χ : HardySpace a b := (InnerProductSpace.toDual ℂ (HardySpace a b)).symm v.toStrongDual
  refine ⟨χ, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℂ (HardySpace a b)).symm v.toStrongDual‖ ≤ C
    rw [LinearIsometryEquiv.norm_map]
    change v.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℂ (HardySpace a b)) C at hv
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  · intro s hs
    let E : WeakDual ℂ (HardySpace a b) → ℂ := fun w => conj (w (evaluationVector s))
    have hE : Continuous E := Complex.continuous_conj.comp (WeakDual.eval_continuous _)
    have hEψ : ∀ n, E (u n) = fourierLaplace (ψ n) s := by
      intro n
      change conj (inner ℂ (ψ n) (evaluationVector s)) = _
      rw [inner_conj_symm]
      exact (evaluationVector_spec hs (ψ n)).symm
    have hEχ : E v = fourierLaplace χ s := by
      rw [evaluationVector_spec hs]
      change conj (v (evaluationVector s)) = inner ℂ (evaluationVector s) χ
      rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)]
      exact inner_conj_symm _ _
    have hEf : Tendsto E (Filter.map u atTop) (𝓝 (f s)) := by
      rw [tendsto_map'_iff]
      have he : E ∘ u = (fun n => fourierLaplace (ψ n) s) := funext hEψ
      rw [he]
      exact hlim s hs
    haveI : NeBot (𝓝 v ⊓ Filter.map u atTop) := hcluster
    have heq : E v = f s := tendsto_nhds_unique
      (hE.continuousAt.tendsto.mono_left inf_le_left) (hEf.mono_left inf_le_right)
    exact hEχ.symm.trans heq

end ConditionalGoldbach
