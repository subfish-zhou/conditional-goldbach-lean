import ConditionalGoldbach

/-! Extra independent semantic checks, not an assertion that TeX can be mechanically parsed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace TexAudit57
open ConditionalGoldbach

def KernelQuadratic (K : ℂ → ℂ → ℂ) (n : ℕ) (z c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, c i * conj (c j) * K (z i) (z j)

-- The Re-only positivity predicate is sufficient only when reality is also justified.
theorem hermitian_quadratic_real (K : ℂ → ℂ → ℂ) (hK : HermitianKernel K)
    (n : ℕ) (z c : Fin n → ℂ) : (KernelQuadratic K n z c).im = 0 := by
  have hc : conj (KernelQuadratic K n z c) = KernelQuadratic K n z c := by
    simp only [KernelQuadratic, map_sum, map_mul, starRingEnd_self_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← hK (z i) (z j)]
    ring
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

theorem character_quadratic_nonnegative_real (N : ℕ) [NeZero N]
    (n : ℕ) (z c : Fin n → ℂ) :
    (KernelQuadratic (fun s t => characterKernel N s (conj t)) n z c).im = 0 ∧
    0 ≤ (KernelQuadratic (fun s t => characterKernel N s (conj t)) n z c).re := by
  exact ⟨hermitian_quadratic_real _ (characterKernel_hermitian N) n z c,
    characterKernel_positive N n z c⟩

-- N>e^10 entails the additional implementation argument a<b; it is not a new hypothesis.
theorem arithmetic_strip_nonempty (N : ℕ) (hN : Real.exp 10 < (N : ℝ)) :
    alpha N < beta := by
  exact (large_parameters hN).2.2

-- The selected operator is uniquely tied to its integral representation.
theorem selected_operator_unique {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (T : HardySpace a beta →L[ℂ] HardySpace a beta)
    (hT : RepresentsKernel ha N K T) : kernelOperator ha N K = T :=
  kernelOperator_eq_of_represents ha N hT

-- This explicitly tests that the default-zero branch cannot substitute for the
-- boundary operator under the paper hypotheses.
theorem actual_operator_integral (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) :=
  (proposition_5_3 N hN hlarge hGRH ha).2.1

-- Original nonzero-eigenvalue products are unchanged by zero padding in a full basis.
theorem zero_padding_product (μ : ℕ → ℝ) (t : ℂ) :
    (∏' j : {j : ℕ // μ j ≠ 0}, (1-t*(μ j : ℂ)^2)) =
      ∏' j : ℕ, (1-t*(μ j : ℂ)^2) := by
  apply tprod_subtype_eq_of_mulSupport_subset (f := fun j : ℕ => 1-t*(μ j : ℂ)^2)
    (s := {j : ℕ | μ j ≠ 0})
  intro j hj
  change μ j ≠ 0
  intro hz
  have hfac : 1-t*(μ j : ℂ)^2 = 1 := by simp [hz]
  exact hj hfac

theorem zero_padding_square_sum (μ : ℕ → ℝ) :
    (∑' j : {j : ℕ // μ j ≠ 0}, μ j^2) = ∑' j : ℕ, μ j^2 := by
  apply tsum_subtype_eq_of_support_subset (f := fun j : ℕ => μ j^2)
    (s := {j : ℕ | μ j ≠ 0})
  intro j hj
  change μ j ≠ 0
  intro hz
  have hzsq : μ j^2 = 0 := by simp [hz]
  exact hj hzsq

end TexAudit57
