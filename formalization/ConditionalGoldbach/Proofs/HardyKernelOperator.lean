import ConditionalGoldbach.Proofs.HardyRawNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! The uniquely represented Hardy kernel operator and compression from the boundary Hilbert space.
These results keep the paper's chosen `kernelOperator` definition: the existence of an operator
representing the actual kernel is a separate analytic obligation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma RepresentsKernel.unique {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    {K : ℂ → ℂ → ℂ} {S T : HardySpace a beta →L[ℂ] HardySpace a beta}
    (hS : RepresentsKernel ha N K S) (hT : RepresentsKernel ha N K T) : S = T := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply fourierLaplace_injective_strip ha
  intro s hs
  exact (hS ψ s hs).trans (hT ψ s hs).symm

lemma kernelOperator_eq_of_represents {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    {K : ℂ → ℂ → ℂ} {T : HardySpace a beta →L[ℂ] HardySpace a beta}
    (hT : RepresentsKernel ha N K T) : kernelOperator ha N K = T := by
  have h : ∃ S, RepresentsKernel ha N K S := ⟨T, hT⟩
  rw [kernelOperator, dite_eq_left h]
  exact RepresentsKernel.unique ha N (Classical.choose_spec h) hT

lemma kernelOperator_represents_of_exists {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    {K : ℂ → ℂ → ℂ} (h : ∃ T, RepresentsKernel ha N K T) :
    RepresentsKernel ha N K (kernelOperator ha N K) := by
  rw [kernelOperator, dite_eq_left h]
  exact Classical.choose_spec h

/-- The two vertical boundaries, equipped with the Hilbert sum norm. -/
abbrev HardyBoundarySpace :=
  WithLp 2 (Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ))

/-- The adjoint of the trace embedding is a left inverse on all Hardy traces. -/
lemma hardyTrace_adjoint_apply {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    (hardyTraceIsometry hab).toContinuousLinearMap.adjoint (hardyTraceIsometry hab ψ) = ψ := by
  have h := congrArg (fun T : HardySpace a b →L[ℂ] HardySpace a b => T ψ)
    (hardyTraceIsometry hab).adjoint_comp_self
  exact h

/-- Compress a bounded boundary operator to the Fourier realization of the Hardy space. -/
def hardyBoundaryCompression {a b : ℝ} (hab : a < b)
    (B : HardyBoundarySpace →L[ℂ] HardyBoundarySpace) : HardySpace a b →L[ℂ] HardySpace a b :=
  (hardyTraceIsometry hab).toContinuousLinearMap.adjoint ∘L B ∘L
    (hardyTraceIsometry hab).toContinuousLinearMap

lemma hardyBoundaryCompression_inner {a b : ℝ} (hab : a < b)
    (B : HardyBoundarySpace →L[ℂ] HardyBoundarySpace) (ψ χ : HardySpace a b) :
    inner ℂ ψ (hardyBoundaryCompression hab B χ) =
      inner ℂ (hardyTraceIsometry hab ψ) (B (hardyTraceIsometry hab χ)) := by
  change inner ℂ ψ ((hardyTraceIsometry hab).toContinuousLinearMap.adjoint
    (B (hardyTraceIsometry hab χ))) = _
  exact (hardyTraceIsometry hab).toContinuousLinearMap.adjoint_inner_right ψ
    (B (hardyTraceIsometry hab χ))

lemma hardyBoundaryCompression_selfAdjoint {a b : ℝ} (hab : a < b)
    {B : HardyBoundarySpace →L[ℂ] HardyBoundarySpace} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (hardyBoundaryCompression hab B) :=
  hB.adjoint_conj (hardyTraceIsometry hab).toContinuousLinearMap

lemma hardyBoundaryCompression_compact {a b : ℝ} (hab : a < b)
    {B : HardyBoundarySpace →L[ℂ] HardyBoundarySpace} (hB : IsCompactOperator B) :
    IsCompactOperator (hardyBoundaryCompression hab B) := by
  exact (hB.comp_clm (hardyTraceIsometry hab).toContinuousLinearMap).clm_comp
    (hardyTraceIsometry hab).toContinuousLinearMap.adjoint

/-- When the boundary operator preserves Hardy traces, compression agrees with restriction. -/
lemma hardyBoundaryCompression_trace {a b : ℝ} (hab : a < b)
    (B : HardyBoundarySpace →L[ℂ] HardyBoundarySpace)
    (hB : ∀ ψ : HardySpace a b,
      B (hardyTraceIsometry hab ψ) ∈ Set.range (hardyTraceIsometry hab))
    (ψ : HardySpace a b) :
    hardyTraceIsometry hab (hardyBoundaryCompression hab B ψ) =
      B (hardyTraceIsometry hab ψ) := by
  obtain ⟨χ, hχ⟩ := hB ψ
  change hardyTraceIsometry hab
    ((hardyTraceIsometry hab).toContinuousLinearMap.adjoint (B (hardyTraceIsometry hab ψ))) = _
  rw [← hχ, hardyTrace_adjoint_apply]

lemma hardyBoundaryCompression_norm_le {a b : ℝ} (hab : a < b)
    (B : HardyBoundarySpace →L[ℂ] HardyBoundarySpace) :
    ‖hardyBoundaryCompression hab B‖ ≤ ‖B‖ := by
  have hJ : ‖(hardyTraceIsometry hab).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ψ
    simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, one_mul, le_refl]
  have hJa : ‖(hardyTraceIsometry hab).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa using hJ
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
  change ‖(hardyTraceIsometry hab).toContinuousLinearMap.adjoint
    (B (hardyTraceIsometry hab ψ))‖ ≤ _
  calc
    _ ≤ ‖(hardyTraceIsometry hab).toContinuousLinearMap.adjoint‖ * ‖B (hardyTraceIsometry hab ψ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖B (hardyTraceIsometry hab ψ)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hJa (norm_nonneg _)
    _ ≤ ‖B‖ * ‖ψ‖ := by simpa using B.le_opNorm (hardyTraceIsometry hab ψ)

end ConditionalGoldbach
