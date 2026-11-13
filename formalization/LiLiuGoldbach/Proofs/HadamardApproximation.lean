import LiLiuGoldbach.Proofs.HadamardDiskFactor

/-! Quantitative finite-zero approximation to the logarithmic-derivative difference. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter MeromorphicOn
namespace LiLiuGoldbach16

lemma logarithmicDerivative_disk_approximation (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (R M : ℝ) (hR : 0 < R) (hM : ‖f 0‖ < M)
    (hbound : ∀ z ∈ sphere (0 : ℂ) (8*R), ‖f z‖ ≤ M)
    (u v : ℂ) (hu : u ∈ ball (0 : ℂ) R) (hv : v ∈ ball (0 : ℂ) R)
    (hfu : f u ≠ 0) (hfv : f v ≠ 0) :
    let D := divisor f (closedBall (0 : ℂ) (4*R))
    let hfin := D.finiteSupport (isCompact_closedBall ..)
    ‖(logDeriv f u-logDeriv f v) -
      ∑ ρ ∈ hfin.toFinset, (D ρ : ℂ)*(1/(u-ρ)-1/(v-ρ))‖ ≤
      (4*Real.log (M/‖f 0‖)/R^2)*‖u-v‖ := by
  intro D hfin
  let P : ℂ → ℂ := ∏ᶠ ρ, (·-ρ)^D ρ
  have ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) (4*R)) := fun z _ => hf.analyticAt z
  have hD : ∀ z, 0 ≤ D z := ha.divisor_nonneg
  have hP : Differentiable ℂ P := fun z => (Function.FactorizedRational.analyticAt (hD z)).differentiableAt
  obtain ⟨g,hg,he,hgn⟩ := entire_disk_factorization f hf hf0 (4*R)
  have he' (z : ℂ) : f z = P z*g z := he z
  have hP0 : P 0 ≠ 0 := fun h => hf0 (by rw [he',h,zero_mul])
  have hg0 : g 0 ≠ 0 := fun h => hf0 (by rw [he',h,mul_zero])
  have hPg0 : ‖f 0‖ = ‖P 0‖*‖g 0‖ := by rw [he',norm_mul]
  have hPboundary (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (8*R)) : ‖P 0‖ ≤ ‖P z‖ := by
    apply factorizedRational_norm_lower D hfin hD (4*R)
    · intro ρ hρ
      exact mem_closedBall_zero_iff.mp (D.supportWithinDomain hρ)
    · have hz' := mem_sphere_zero_iff_norm.mp hz
      linarith
  have hgBoundary (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (8*R)) : ‖g z‖ ≤ M/‖P 0‖ := by
    apply (le_div_iff₀ (norm_pos_iff.mpr hP0)).mpr
    calc
      _ = ‖P 0‖*‖g z‖ := mul_comm _ _
      _ ≤ ‖P z‖*‖g z‖ := mul_le_mul_of_nonneg_right (hPboundary z hz) (norm_nonneg _)
      _ = ‖f z‖ := by rw [he',norm_mul]
      _ ≤ M := hbound z hz
  have hgb (z : ℂ) (hz : z ∈ ball (0 : ℂ) (4*R)) : ‖g z‖ ≤ M/‖P 0‖ := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (show DiffContOnCl ℂ g (ball (0 : ℂ) (8*R)) from ⟨hg.differentiableOn,hg.continuous.continuousOn⟩)
    · rw [frontier_ball (0 : ℂ) (by linarith : (8*R) ≠ 0)]
      exact hgBoundary
    · rw [closure_ball (0 : ℂ) (by linarith : (8*R) ≠ 0)]
      exact mem_closedBall_zero_iff.mpr (by have hh := mem_ball_zero_iff.mp hz; linarith)
  obtain ⟨q,hq0,hqd,hqe⟩ := zero_free_disk_log g (4*R) (by linarith)
    (fun z _ => hg.analyticAt z) (fun z hz => hgn z (ball_subset_closedBall hz))
  have hqDiff : DifferentiableOn ℂ q (ball (0 : ℂ) (4*R)) :=
    fun z hz => (hqd z hz).differentiableAt.differentiableWithinAt
  have hq : AnalyticOnNhd ℂ q (ball (0 : ℂ) (4*R)) := hqDiff.analyticOnNhd isOpen_ball
  have hL : 0 < Real.log (M/‖f 0‖) := Real.log_pos ((one_lt_div (norm_pos_iff.mpr hf0)).mpr hM)
  have hqBound (z : ℂ) (hz : z ∈ ball (0 : ℂ) (4*R)) : (q z).re ≤ Real.log (M/‖f 0‖) := by
    have hh := logarithm_re_le_of_bounds g q (M/‖P 0‖) ‖g 0‖ (norm_pos_iff.mpr hg0) le_rfl z
      (hgn z (ball_subset_closedBall hz)) (hgb z hz) (hqe z hz)
    simpa only [div_div, ← hPg0] using hh
  have hvar := logarithm_derivative_variation q R (Real.log (M/‖f 0‖)) hR hL hq hq0 hqBound u v hu hv
  have hu4 : u ∈ ball (0 : ℂ) (4*R) := ball_subset_ball (by linarith) hu
  have hv4 : v ∈ ball (0 : ℂ) (4*R) := ball_subset_ball (by linarith) hv
  rw [(hqd u hu4).deriv,(hqd v hv4).deriv] at hvar
  have huP : P u ≠ 0 := fun h => hfu (by rw [he',h,zero_mul])
  have hvP : P v ≠ 0 := fun h => hfv (by rw [he',h,zero_mul])
  have hfEq : f = P*g := funext he'
  have hdu := logDeriv_mul u huP (hgn u (ball_subset_closedBall hu4)) (hP u) (hg u)
  have hdv := logDeriv_mul v hvP (hgn v (ball_subset_closedBall hv4)) (hP v) (hg v)
  rw [← hfEq,factorizedRational_logDeriv D hfin hD u huP] at hdu
  rw [← hfEq,factorizedRational_logDeriv D hfin hD v hvP] at hdv
  have heq : (logDeriv f u-logDeriv f v) -
      ∑ ρ ∈ hfin.toFinset, (D ρ : ℂ)*(1/(u-ρ)-1/(v-ρ)) = deriv g u/g u-deriv g v/g v := by
    simp_rw [mul_sub,mul_one_div,Finset.sum_sub_distrib]
    rw [hdu,hdv]
    change (_+deriv g u/g u)-(_+deriv g v/g v)-(_-_) = _
    ring
  rw [heq]
  exact hvar

end LiLiuGoldbach16
