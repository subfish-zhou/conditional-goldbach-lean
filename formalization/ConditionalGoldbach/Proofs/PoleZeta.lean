import ConditionalGoldbach.Proofs.PoleLogDerivative
import ConditionalGoldbach.Proofs.DensityResidue
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! The double pole of the derivative of zeta's logarithmic derivative. -/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Set Complex Filter
namespace ConditionalGoldbach

lemma riemannZeta_order_one : meromorphicOrderAt riemannZeta 1 = (-1:ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff (riemannZeta_meromorphicAt_re_pos (by norm_num))).mpr
  refine ⟨riemannZeta₁,differentiable_riemannZeta₁.analyticAt 1,by simp,?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with z hz
  simpa only [zpow_neg_one,smul_eq_mul] using riemannZeta_eq_inv_sub_mul hz

lemma zeta_logDeriv_deriv_double_pole :
    Tendsto (fun x : ℝ => (x:ℂ)^2*deriv (logDeriv riemannZeta) (1+2*(x:ℂ)))
      (𝓝[>] 0) (𝓝 (1/4:ℂ)) := by
  have hmap : Tendsto (fun x : ℝ => (1:ℂ)+2*(x:ℂ)) (𝓝[>] 0) (𝓝[≠] (1:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun x : ℝ => (1:ℂ)+2*(x:ℂ)) := by fun_prop
      simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change (1:ℂ)+2*(x:ℂ) ≠ 1
      have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 from ne_of_gt hx)
      simp [hx0]
  have hh := (deriv_logDeriv_double_pole_tendsto
    (riemannZeta_meromorphicAt_re_pos (by norm_num)) (-1) riemannZeta_order_one).comp hmap
  have hlim := hh.const_mul (1/4:ℂ)
  convert hlim using 1
  · funext x
    simp only [Function.comp_def]
    ring
  · norm_num

end ConditionalGoldbach
