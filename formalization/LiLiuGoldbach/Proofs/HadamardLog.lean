import LiLiuGoldbach.Proofs.LogDerivativeDisk

/-! The vanishing error in Hadamard's difference formula: Cauchy estimates for a holomorphic logarithm. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace LiLiuGoldbach16

lemma logarithm_derivative_variation (g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hg : AnalyticOnNhd ℂ g (ball 0 (4*R))) (hg0 : g 0 = 0)
    (hb : ∀ z ∈ ball (0 : ℂ) (4*R), (g z).re ≤ M)
    (u v : ℂ) (hu : u ∈ ball (0 : ℂ) R) (hv : v ∈ ball (0 : ℂ) R) :
    ‖deriv g u-deriv g v‖ ≤ (4*M/R^2)*‖u-v‖ := by
  have hnorm (z : ℂ) (hz : ‖z‖ ≤ 2*R) : ‖g z‖ ≤ 2*M := by
    have hzr : z ∈ ball (0 : ℂ) (4*R) := mem_ball_zero_iff.mpr (by linarith)
    have hh := Complex.borelCaratheodory_zero hM hg.differentiableOn hb (by linarith) hzr hg0
    apply hh.trans
    apply (div_le_iff₀ (by linarith : 0 < 4*R-‖z‖)).mpr
    nlinarith
  have hsecond (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : ‖deriv (deriv g) z‖ ≤ 4*M/R^2 := by
    have hzR := mem_ball_zero_iff.mp hz
    have hsub : closedBall z R ⊆ ball (0 : ℂ) (4*R) := by
      intro w hw
      have hdist : ‖w-z‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hw
      have hh := norm_add_le (w-z) z
      rw [sub_add_cancel] at hh
      apply mem_ball_zero_iff.mpr
      linarith
    have hdiff : DiffContOnCl ℂ g (ball z R) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hR.ne']
      exact hg.differentiableOn.mono hsub
    have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR hdiff
      (C := 2*M) (by
        intro w hw
        apply hnorm
        have hd : ‖w-z‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hw
        have hn := norm_add_le (w-z) z
        rw [sub_add_cancel,hd] at hn
        linarith)
    norm_num [iteratedDeriv_succ, Nat.factorial, ← mul_assoc] at hh
    exact hh
  apply (convex_ball (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le _ hsecond hv hu
  intro z hz
  exact (hg.deriv z (ball_subset_ball (by linarith : R ≤ 4*R) hz)).differentiableAt

end LiLiuGoldbach16
