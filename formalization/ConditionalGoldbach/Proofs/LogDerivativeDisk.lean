module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Quantitative logarithmic derivatives on a zero-free disk, via a genuine analytic logarithm. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex Metric
namespace ConditionalGoldbach

lemma zero_free_disk_log (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g 0 = 0 ∧
      (∀ z ∈ ball 0 R, HasDerivAt g (deriv f z / f z) z) ∧
      (∀ z ∈ ball 0 R, Complex.exp (g z) = f z / f 0) := by
  have hld : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball 0 R) :=
    hf.deriv.differentiableOn.div hf.differentiableOn hn
  obtain ⟨g,hg0,hg⟩ := hld.isExactOn_ball.with_val_at 0 0
  have hzero (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      HasDerivAt (fun z => Complex.exp (-g z) * f z) 0 z := by
    convert ((hg z hz).neg.cexp).mul ((hf z hz).differentiableAt.hasDerivAt) using 1
    field_simp [hn z hz]
    ring
  have heq (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      Complex.exp (-g z) * f z = f 0 := by
    have h := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
      (fun z hz => (hzero z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hzero z hz).deriv) hz (mem_ball_self hR)
    simpa only [hg0, neg_zero, Complex.exp_zero, one_mul] using h
  refine ⟨g,hg0,hg,fun z hz => ?_⟩
  have hc := hn 0 (mem_ball_self hR)
  have hh := heq z hz
  rw [Complex.exp_neg] at hh
  apply (eq_div_iff hc).mpr
  field_simp [Complex.exp_ne_zero] at hh
  linear_combination -hh

lemma logarithm_re_le_of_bounds (f g : ℂ → ℂ) (U l : ℝ) (hl : 0 < l)
    (hlf : l ≤ ‖f 0‖) (z : ℂ) (hn : f z ≠ 0) (hb : ‖f z‖ ≤ U)
    (hg : Complex.exp (g z) = f z / f 0) : (g z).re ≤ Real.log (U/l) := by
  have hf0 : 0 < ‖f 0‖ := hl.trans_le hlf
  have hp : 0 < ‖f z‖ / ‖f 0‖ := div_pos (norm_pos_iff.mpr hn) hf0
  have he := congrArg (fun w : ℂ => Real.log ‖w‖) hg
  rw [Complex.norm_exp, Real.log_exp, norm_div] at he
  rw [he]
  apply Real.log_le_log hp
  calc
    _ ≤ U / ‖f 0‖ := div_le_div_of_nonneg_right hb hf0.le
    _ ≤ U / l := div_le_div_of_nonneg_left ((norm_nonneg _).trans hb) hl hlf

lemma logDerivative_disk_bound (f : ℂ → ℂ) (R r U l : ℝ)
    (hR : 0 < R) (_hr : 0 ≤ r) (hrR : r < R) (hl : 0 < l) (hlU : l < U)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hlf : l ≤ ‖f 0‖) (hbound : ∀ z ∈ ball 0 R, ‖f z‖ ≤ U)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖deriv f z / f z‖ ≤ 8 * R / (R-r)^2 * Real.log (U/l) := by
  obtain ⟨g,hg0,hg,hge⟩ := zero_free_disk_log f R hR hf hn
  let M : ℝ := Real.log (U/l)
  let ρ : ℝ := (R-r)/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hM : 0 < M := Real.log_pos ((one_lt_div hl).mpr hlU)
  have hgd : DifferentiableOn ℂ g (ball 0 R) :=
    fun v hv => (hg v hv).differentiableAt.differentiableWithinAt
  have hgB (v : ℂ) (hv : v ∈ ball (0 : ℂ) R) :
      ‖g v‖ ≤ 2*M*‖v‖/(R-‖v‖) :=
    Complex.borelCaratheodory_zero hM hgd
      (fun v hv => logarithm_re_le_of_bounds f g U l hl hlf v (hn v hv) (hbound v hv) (hge v hv)) hR hv hg0
  have hsub : closedBall z ρ ⊆ ball (0 : ℂ) R := by
    intro v hv
    have hdist : ‖v-z‖ ≤ ρ := by simpa only [mem_closedBall, dist_eq_norm] using hv
    have hvn := norm_add_le (v-z) z
    rw [sub_add_cancel] at hvn
    apply mem_ball_zero_iff.mpr
    dsimp [ρ] at hdist
    linarith
  have hnorm : ∀ v ∈ sphere z ρ, ‖g v‖ ≤ 4*M*R/(R-r) := by
    intro v hv
    have hclose : v ∈ closedBall z ρ := sphere_subset_closedBall hv
    have hvball := hsub hclose
    have hdist : ‖v-z‖ ≤ ρ := by simpa only [mem_closedBall, dist_eq_norm] using hclose
    have hvn := norm_add_le (v-z) z
    rw [sub_add_cancel] at hvn
    have hvmax : ‖v‖ ≤ (R+r)/2 := by dsimp [ρ] at hdist; linarith
    have hden : 0 < R-‖v‖ := by have := mem_ball_zero_iff.mp hvball; linarith
    apply (hgB v hvball).trans
    apply (div_le_div_iff₀ hden (sub_pos.mpr hrR)).mpr
    nlinarith [norm_nonneg v, mul_nonneg hM.le (sub_nonneg.mpr hrR.le),
      mul_nonneg hM.le (sub_nonneg.mpr hvmax)]
  have hc : DiffContOnCl ℂ g (ball z ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hρ.ne']
    exact hgd.mono hsub
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hc hnorm
  rw [(hg z (mem_ball_zero_iff.mpr (hz.trans_lt hrR))).deriv] at hd
  convert hd using 1
  dsimp [ρ,M]
  field_simp
  ring

end ConditionalGoldbach
