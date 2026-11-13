import LiLiuGoldbach.Proofs.HadamardFactors

/-! Remove exactly the zeros in a disk, retaining an entire quotient and correct point values. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter MeromorphicOn
namespace LiLiuGoldbach16

lemma entire_disk_factorization (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (r : ℝ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ z, f z = (∏ᶠ u, (·-u)^(divisor f (closedBall 0 r) u)) z * g z) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) := by
  let D := divisor f (closedBall (0 : ℂ) r)
  have ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := fun z _ => hf.analyticAt z
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall ..)
  have hD : ∀ z, 0 ≤ D z := ha.divisor_nonneg
  have hDeq (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      (D z : WithTop ℤ) = meromorphicOrderAt f z := by
    change ((divisor f (closedBall (0 : ℂ) r) z : ℤ) : WithTop ℤ) = _
    rw [ha.meromorphicOn.divisor_apply hz]
    lift meromorphicOrderAt f z to ℤ using entire_order_ne_top f hf hf0 z with n hn
    simp
  have hord (z : ℂ) : (D z : WithTop ℤ) ≤ meromorphicOrderAt f z := by
    by_cases hz : z ∈ closedBall (0 : ℂ) r
    · exact (hDeq z hz).le
    · rw [D.apply_eq_zero_of_notMem hz,WithTop.coe_zero]
      exact (hf.analyticAt z).meromorphicOrderAt_nonneg
  obtain ⟨g,hg,he,hgo⟩ := entire_factorized_quotient f hf hf0 D hfin hD hord
  refine ⟨g,hg,he,?_⟩
  intro z hz
  apply (hg.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  rw [hgo, hDeq z hz]
  lift meromorphicOrderAt f z to ℤ using entire_order_ne_top f hf hf0 z with n hn
  norm_cast
  exact sub_self n

end LiLiuGoldbach16
