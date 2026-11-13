import ConditionalGoldbach.Proofs.BetaIntegrals
import ConditionalGoldbach.Proofs.BetaIdentity

/-! The inner Beta integrals in the convolution–Mellin calculation, including norm integrals. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma beta_real_integrand_re (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (s z : ℂ) :
    ‖(u : ℂ)^(-1/2-s) * (v : ℂ)^(-1/2-z)‖ =
      ((u : ℂ)^(-1/2-(s.re : ℂ)) * (v : ℂ)^(-1/2-(z.re : ℂ))).re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hs : (-1/2-(s.re : ℂ)) = ((-1/2-s.re : ℝ) : ℂ) := by push_cast; rfl
  have hz : (-1/2-(z.re : ℂ)) = ((-1/2-z.re : ℝ) : ℂ) := by push_cast; rfl
  rw [hs, hz, ← Complex.ofReal_cpow hu.le, ← Complex.ofReal_cpow hv.le,
    ← ofReal_mul, ofReal_re]
  congr 1 <;> simp

lemma beta_difference_norm_integral (r : ℝ) (hr : 0 < r) (s z : ℂ)
    (hd : (s,z) ∈ betaDomain) :
    (∫ u in Ioi (0 : ℝ), ‖(u : ℂ)^(-1/2-s) * (u+r : ℂ)^(-1/2-z)‖) =
      r ^ (-(s.re+z.re)) * (betaIntegral ((1/2 : ℝ)-s.re) (s.re+z.re)).re := by
  have hd' : ((s.re : ℂ),(z.re : ℂ)) ∈ betaDomain := by
    simpa only [betaDomain, mem_setOf_eq, ofReal_re, add_re] using hd
  calc
    _ = ∫ u in Ioi (0 : ℝ),
        ((u : ℂ)^(-1/2-(s.re : ℂ)) * (u+r : ℂ)^(-1/2-(z.re : ℂ))).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simpa only [ofReal_add] using beta_real_integrand_re u (u+r) hu (add_pos hu hr) s z
    _ = (∫ u in Ioi (0 : ℝ),
        (u : ℂ)^(-1/2-(s.re : ℂ)) * (u+r : ℂ)^(-1/2-(z.re : ℂ))).re :=
      integral_re (beta_difference_integrable r hr _ _ hd')
    _ = _ := by
      rw [beta_difference_integral r hr]
      have he : -((s.re : ℂ)+(z.re : ℂ)) = (-(s.re+z.re) : ℝ) := by push_cast; rfl
      rw [he, ← Complex.ofReal_cpow hr.le]
      simp only [Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      congr 2 <;> push_cast <;> rfl

lemma beta_sum_norm_integral (r : ℝ) (hr : 0 < r) (s z : ℂ)
    (hd : (s,z) ∈ betaDomain) :
    (∫ u in Ioo (0 : ℝ) r, ‖(u : ℂ)^(-1/2-s) * (r-u : ℂ)^(-1/2-z)‖) =
      r ^ (-(s.re+z.re)) * (betaIntegral ((1/2 : ℝ)-s.re) ((1/2 : ℝ)-z.re)).re := by
  have hd' : ((s.re : ℂ),(z.re : ℂ)) ∈ betaDomain := by
    simpa only [betaDomain, mem_setOf_eq, ofReal_re, add_re] using hd
  calc
    _ = ∫ u in Ioo (0 : ℝ) r,
        ((u : ℂ)^(-1/2-(s.re : ℂ)) * (r-u : ℂ)^(-1/2-(z.re : ℂ))).re := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      simpa only [ofReal_sub] using beta_real_integrand_re u (r-u) hu.1 (sub_pos.mpr hu.2) s z
    _ = (∫ u in Ioo (0 : ℝ) r,
        (u : ℂ)^(-1/2-(s.re : ℂ)) * (r-u : ℂ)^(-1/2-(z.re : ℂ))).re :=
      integral_re (beta_sum_integrable r hr _ _ hd')
    _ = _ := by
      rw [beta_sum_integral r hr]
      have he : -((s.re : ℂ)+(z.re : ℂ)) = (-(s.re+z.re) : ℝ) := by push_cast; rfl
      rw [he, ← Complex.ofReal_cpow hr.le]
      simp only [Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      congr 2 <;> push_cast <;> rfl

lemma convolution_betaDomain (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9)
    (s w : ℂ) (hs : s.re = σ) (hw : w.re = 2*σ) :
    (s, 1/2-w) ∈ betaDomain := by
  change s.re < 1/2 ∧ (1/2-w).re < 1/2 ∧ 0 < (s+(1/2-w)).re
  norm_num [hs, hw]
  constructor
  · linarith
  constructor <;> linarith

lemma convolution_inner_beta_sum (r : ℝ) (hr : 0 < r) (s w : ℂ) :
    (∫ u in Ioo (0 : ℝ) r, (u : ℂ)^(-1/2-s) * (r-u : ℂ)^(w-1)) =
      (r : ℂ)^(w-1/2-s) * betaIntegral (1/2-s) w := by
  have he : -1/2-(1/2-w) = w-1 := by ring
  have he' : -(s+(1/2-w)) = w-1/2-s := by ring
  have he'' : (1/2 : ℂ)-(1/2-w) = w := by ring
  simpa only [he, he', he''] using beta_sum_integral r hr s (1/2-w)

lemma convolution_inner_beta_difference (r : ℝ) (hr : 0 < r) (s w : ℂ) :
    (∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1/2-s) * (u+r : ℂ)^(w-1)) =
      (r : ℂ)^(w-1/2-s) * betaIntegral (1/2-s) (1/2+s-w) := by
  have he : -1/2-(1/2-w) = w-1 := by ring
  have he' : -(s+(1/2-w)) = w-1/2-s := by ring
  have he'' : s+(1/2-w) = 1/2+s-w := by ring
  have h := beta_difference_integral r hr s (1/2-w)
  rw [he, he'] at h
  simpa only [he''] using h

end ConditionalGoldbach
