module

public import ConditionalGoldbach.Definitions.Asymptotics
public import ConditionalGoldbach.Proofs.HardyEvaluation
public import ConditionalGoldbach.Proofs.HardyKernelOperator

/-! Double evaluation of a represented Hermitian kernel.
The Hardy membership and exact boundary traces of each column are explicit hypotheses:
these are the analytic inputs required before double reproduction can be used. -/
public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma represented_kernel_pairing_of_columns {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (hK : HermitianKernel K)
    (T : HardySpace a beta →L[ℂ] HardySpace a beta) (hT : RepresentsKernel ha N K T)
    (hcol : ∀ s ∈ strip a beta, ∃ g : HardySpace a beta,
      (∀ z ∈ strip a beta, fourierLaplace g z = K z s) ∧
      ((boundaryTraces ha g).1 =ᵐ[volume] fun t => K (line a t) s) ∧
      ((boundaryTraces ha g).2 =ᵐ[volume] fun t => K (line beta t) s))
    (s z : ℂ) (hs : s ∈ strip a beta) (hz : z ∈ strip a beta) :
    K s z = paperInner (T (evaluationVector z)) (evaluationVector s) := by
  obtain ⟨g, hg, hga, hgb⟩ := hcol s hs
  rw [← evaluationVector_spec hs, hT _ s hs]
  have hi := lemma_5_2_boundary_inner a beta ha (evaluationVector z) g
  have hk : kernelAction ha N K (evaluationVector z) s =
      paperInner (evaluationVector z) g := by
    rw [hi]
    unfold kernelAction
    congr 1
    · apply integral_congr_ae
      filter_upwards [hga] with t ht
      rw [ht, hK s (line a t), mul_comm]
    · apply integral_congr_ae
      filter_upwards [hgb] with t ht
      rw [ht, hK s (line beta t), mul_comm]
  rw [hk]
  calc
    K s z = conj (K z s) := hK s z
    _ = conj (paperInner g (evaluationVector z)) := by rw [← evaluationVector_spec hz, hg z hz]
    _ = paperInner (evaluationVector z) g := by
      exact inner_conj_symm _ _

lemma kernelOperator_pairing_of_columns {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (hK : HermitianKernel K)
    (hex : ∃ T, RepresentsKernel ha N K T)
    (hcol : ∀ s ∈ strip a beta, ∃ g : HardySpace a beta,
      (∀ z ∈ strip a beta, fourierLaplace g z = K z s) ∧
      ((boundaryTraces ha g).1 =ᵐ[volume] fun t => K (line a t) s) ∧
      ((boundaryTraces ha g).2 =ᵐ[volume] fun t => K (line beta t) s))
    (s z : ℂ) (hs : s ∈ strip a beta) (hz : z ∈ strip a beta) :
    K s z = paperInner (kernelOperator ha N K (evaluationVector z)) (evaluationVector s) :=
  represented_kernel_pairing_of_columns ha N K hK _
    (kernelOperator_represents_of_exists ha N hex) hcol s z hs hz

end ConditionalGoldbach
