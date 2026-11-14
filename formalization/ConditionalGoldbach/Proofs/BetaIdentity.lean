module

public import ConditionalGoldbach.Definitions.Model
import Mathlib.Tactic.NormNum.RealSqrt

/-! The beta-kernel Gamma quotient, with all arguments in their original domain. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma gamma_reflection_inverse {a : ℂ} (ha : 0 < a.re) (ha1 : a.re < 1) :
    (Gamma (1 - a))⁻¹ = Gamma a * Complex.sin (Real.pi * a) / Real.pi := by
  have hga := Complex.Gamma_ne_zero_of_re_pos ha
  have hgb := Complex.Gamma_ne_zero_of_re_pos (s := 1 - a) (by simp; linarith)
  have hR := Complex.Gamma_mul_Gamma_one_sub a
  have hs : Complex.sin (Real.pi * a) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at hR
    exact (mul_ne_zero hga hgb) hR
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (eq_div_iff hπ).2
  calc
    _ = (Gamma (1 - a))⁻¹ * ((Gamma a * Gamma (1 - a)) * Complex.sin (Real.pi * a)) := by
      congr 1
      exact ((eq_div_iff hs).mp hR).symm
    _ = _ := by field_simp

lemma gamma_half_ratio {a : ℂ} (ha : 0 < a.re) (ha1 : a.re < 1) :
    Gamma ((a + 1) / 2) / Gamma (1 - a / 2) =
      (2 : ℂ) ^ (1 - a) / Real.sqrt Real.pi * Gamma a * Complex.sin (Real.pi * a / 2) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (Real.sqrt Real.pi : ℂ) ^ 2 = Real.pi := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hr : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [div_eq_mul_inv, gamma_reflection_inverse (a := a / 2)
    (by simp; linarith) (by simp; linarith)]
  have hdup := Complex.Gamma_mul_Gamma_add_half (a / 2)
  have he1 : a / 2 + 1 / 2 = (a + 1) / 2 := by ring
  have he2 : 2 * (a / 2) = a := by ring
  rw [he1, he2] at hdup
  calc
    _ = (Gamma (a / 2) * Gamma ((a + 1) / 2)) * Complex.sin (Real.pi * a / 2) / Real.pi := by
      rw [show (Real.pi : ℂ) * (a / 2) = Real.pi * a / 2 by ring]
      ring
    _ = _ := by
      rw [hdup, ← hsq]
      field_simp

lemma beta_sine_identity (x y : ℂ) :
    Complex.sin x + Complex.sin y - Complex.sin (x + y) =
      4 * Complex.sin (x / 2) * Complex.sin (y / 2) * Complex.sin ((x + y) / 2) := by
  have hd : Complex.sin (x + y) = 2 * Complex.sin ((x + y) / 2) * Complex.cos ((x + y) / 2) := by
    convert Complex.sin_two_mul ((x + y) / 2) using 1
    congr 1
    ring
  rw [Complex.sin_add_sin, hd]
  calc
    _ = 2 * Complex.sin ((x + y) / 2) *
        (Complex.cos ((x - y) / 2) - Complex.cos ((x + y) / 2)) := by ring
    _ = _ := by
      rw [Complex.cos_sub_cos,
        show ((x - y) / 2 + (x + y) / 2) / 2 = x / 2 by ring,
        show ((x - y) / 2 - (x + y) / 2) / 2 = -(y / 2) by ring,
        Complex.sin_neg]
      ring

lemma beta_triangle_gamma {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (habc : a + b + c = 1) :
    betaIntegral a b + betaIntegral c b - betaIntegral a c =
      Gamma a * Gamma b * Gamma c / Real.pi *
        (Complex.sin (Real.pi * a) + Complex.sin (Real.pi * c) - Complex.sin (Real.pi * b)) := by
  have hr := congrArg Complex.re habc
  simp only [add_re, one_re] at hr
  have ha1 : a.re < 1 := by linarith
  have hb1 : b.re < 1 := by linarith
  have hc1 : c.re < 1 := by linarith
  have hab : a + b = 1 - c := by linear_combination habc
  have hcb : c + b = 1 - a := by linear_combination habc
  have hac : a + c = 1 - b := by linear_combination habc
  rw [Complex.betaIntegral_eq_Gamma_mul_div a b ha hb,
    Complex.betaIntegral_eq_Gamma_mul_div c b hc hb,
    Complex.betaIntegral_eq_Gamma_mul_div a c ha hc, hab, hcb, hac]
  simp only [div_eq_mul_inv]
  rw [gamma_reflection_inverse hc hc1, gamma_reflection_inverse ha ha1,
    gamma_reflection_inverse hb hb1]
  ring

lemma beta_triangle_sine {a b c : ℂ} (habc : a + b + c = 1) :
    Complex.sin (Real.pi * a) + Complex.sin (Real.pi * c) - Complex.sin (Real.pi * b) =
      4 * Complex.sin (Real.pi * a / 2) * Complex.sin (Real.pi * c / 2) *
        Complex.cos (Real.pi * b / 2) := by
  have hsb : Complex.sin (Real.pi * b) = Complex.sin (Real.pi * a + Real.pi * c) := by
    rw [← Complex.sin_pi_sub (Real.pi * a + Real.pi * c)]
    congr 1
    linear_combination (Real.pi : ℂ) * habc
  have hsc : Complex.sin ((Real.pi * a + Real.pi * c) / 2) = Complex.cos (Real.pi * b / 2) := by
    rw [← Complex.sin_pi_div_two_sub (Real.pi * b / 2)]
    congr 1
    linear_combination (Real.pi / 2 : ℂ) * habc
  rw [hsb, beta_sine_identity, hsc]

lemma gammaQuotient_half_ratio (s : ℂ) :
    gammaQuotient s = Gamma (((1 / 2 - s) + 1) / 2) / Gamma (1 - (1 / 2 - s) / 2) := by
  unfold gammaQuotient
  congr 2 <;> ring

lemma betaKernel_gamma_identity (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    betaKernel s z = (2 : ℂ) ^ (1 - (s + z)) * Gamma (s + z) *
      Complex.cos (Real.pi * (s + z) / 2) * gammaQuotient s * gammaQuotient z := by
  let a : ℂ := 1 / 2 - s
  let b : ℂ := s + z
  let c : ℂ := 1 / 2 - z
  have ha : 0 < a.re := by dsimp [a]; simp; linarith [hd.1]
  have hb : 0 < b.re := hd.2.2
  have hc : 0 < c.re := by dsimp [c]; simp; linarith [hd.2.1]
  have habc : a + b + c = 1 := by dsimp [a, b, c]; ring
  have hr := congrArg Complex.re habc
  simp only [add_re, one_re] at hr
  have ha1 : a.re < 1 := by linarith
  have hc1 : c.re < 1 := by linarith
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (Real.sqrt Real.pi : ℂ) ^ 2 = Real.pi := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hrt : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpow : (2 : ℂ) ^ (1 - b) * (2 : ℂ) ^ (1 - a) * (2 : ℂ) ^ (1 - c) = 4 := by
    rw [← Complex.cpow_add _ _ (by norm_num), ← Complex.cpow_add _ _ (by norm_num)]
    have he : (1 - b) + (1 - a) + (1 - c) = (2 : ℂ) := by linear_combination -habc
    rw [he]
    norm_num
  have hβ := beta_triangle_gamma ha hb hc habc
  rw [beta_triangle_sine habc] at hβ
  change betaIntegral a b + betaIntegral c b - betaIntegral a c = _
  rw [hβ, gammaQuotient_half_ratio s, gammaQuotient_half_ratio z,
    gamma_half_ratio ha ha1, gamma_half_ratio hc hc1]
  change Gamma a * Gamma b * Gamma c / Real.pi *
      (4 * Complex.sin (Real.pi * a / 2) * Complex.sin (Real.pi * c / 2) * Complex.cos (Real.pi * b / 2)) =
    (2 : ℂ) ^ (1 - b) * Gamma b * Complex.cos (Real.pi * b / 2) *
      ((2 : ℂ) ^ (1 - a) / Real.sqrt Real.pi * Gamma a * Complex.sin (Real.pi * a / 2)) *
      ((2 : ℂ) ^ (1 - c) / Real.sqrt Real.pi * Gamma c * Complex.sin (Real.pi * c / 2))
  rw [← hsq]
  field_simp
  rw [hsq]
  linear_combination -(Gamma a * Gamma b * Gamma c * Complex.sin (Real.pi * a / 2) *
    Complex.sin (Real.pi * c / 2) * Complex.cos (Real.pi * b / 2)) * hpow

lemma betaIntegral_real (a b : ℝ) :
    betaIntegral (a : ℂ) (b : ℂ) =
      ((∫ u in Ioo (0 : ℝ) 1, Real.rpow u (a - 1) * Real.rpow (1 - u) (b - 1) : ℝ) : ℂ) := by
  rw [betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [Complex.ofReal_mul]
  change (u : ℂ) ^ ((a : ℂ) - 1) * (1 - (u : ℂ)) ^ ((b : ℂ) - 1) =
    ((u ^ (a - 1) : ℝ) : ℂ) * (((1 - u) ^ (b - 1) : ℝ) : ℂ)
  rw [Complex.ofReal_cpow hu.1.le, Complex.ofReal_cpow (sub_pos.mpr hu.2).le]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]

lemma betaIntegral_real_nonneg (a b : ℝ) : 0 ≤ (betaIntegral (a : ℂ) (b : ℂ)).re := by
  rw [betaIntegral_real, Complex.ofReal_re]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (sub_pos.mpr hu.2).le _)

lemma norm_betaIntegral_le_real (s z : ℂ) :
    ‖betaIntegral s z‖ ≤ (betaIntegral (s.re : ℂ) (z.re : ℂ)).re := by
  rw [betaIntegral_real, Complex.ofReal_re]
  unfold betaIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ u in Ioo (0 : ℝ) 1, ‖(u : ℂ) ^ (s - 1) * (1 - (u : ℂ)) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1]
      rw [show (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hu.2)]
      simp

lemma betaKernel_vertical_bound (s z : ℂ) (σ : ℝ) (hs : s.re = σ) (hz : z.re = σ) :
    ‖betaKernel s z‖ ≤ ‖2 * betaIntegral (1 / 2 - σ) (2 * σ) +
      betaIntegral (1 / 2 - σ) (1 / 2 - σ)‖ := by
  have h1 := norm_betaIntegral_le_real (1 / 2 - s) (s + z)
  have h2 := norm_betaIntegral_le_real (1 / 2 - z) (s + z)
  have h3 := norm_betaIntegral_le_real (1 / 2 - s) (1 / 2 - z)
  have hre1 : (1 / 2 - s).re = 1 / 2 - σ := by norm_num [hs]
  have hre2 : (1 / 2 - z).re = 1 / 2 - σ := by norm_num [hz]
  have hsum : (s + z).re = 2 * σ := by simp only [add_re, hs, hz]; ring
  rw [hre1, hsum] at h1
  rw [hre2, hsum] at h2
  rw [hre1, hre2] at h3
  have hnorm :
      ‖2 * betaIntegral ((1 / 2 - σ : ℝ) : ℂ) ((2 * σ : ℝ) : ℂ) +
        betaIntegral ((1 / 2 - σ : ℝ) : ℂ) ((1 / 2 - σ : ℝ) : ℂ)‖ =
      2 * (betaIntegral ((1 / 2 - σ : ℝ) : ℂ) ((2 * σ : ℝ) : ℂ)).re +
        (betaIntegral ((1 / 2 - σ : ℝ) : ℂ) ((1 / 2 - σ : ℝ) : ℂ)).re := by
    have hn1 := betaIntegral_real_nonneg (1 / 2 - σ) (2 * σ)
    have hn2 := betaIntegral_real_nonneg (1 / 2 - σ) (1 / 2 - σ)
    simp only [betaIntegral_real, Complex.ofReal_re] at hn1 hn2 ⊢
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have heq : ((1 / 2 - σ : ℝ) : ℂ) = 1 / 2 - σ := by push_cast; rfl
  have heq2 : ((2 * σ : ℝ) : ℂ) = 2 * (σ : ℂ) := by push_cast; rfl
  rw [heq, heq2] at hnorm
  rw [hnorm]
  unfold betaKernel
  calc
    _ ≤ ‖betaIntegral (1 / 2 - s) (s + z) + betaIntegral (1 / 2 - z) (s + z)‖ +
        ‖betaIntegral (1 / 2 - s) (1 / 2 - z)‖ := norm_sub_le _ _
    _ ≤ (‖betaIntegral (1 / 2 - s) (s + z)‖ + ‖betaIntegral (1 / 2 - z) (s + z)‖) +
        ‖betaIntegral (1 / 2 - s) (1 / 2 - z)‖ := by
          linarith [norm_add_le (betaIntegral (1 / 2 - s) (s + z))
            (betaIntegral (1 / 2 - z) (s + z))]
    _ ≤ _ := by simp only [heq, heq2] at h1 h2 h3; linarith

theorem lemma_4_2 (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    betaKernel s z = (2 : ℂ) ^ (1 - (s + z)) * Gamma (s + z) *
      Complex.cos (Real.pi * (s + z) / 2) * gammaQuotient s * gammaQuotient z ∧
    (∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 → s.re = σ → z.re = σ →
      ‖betaKernel s z‖ ≤ ‖2 * betaIntegral (1 / 2 - σ) (2 * σ) +
        betaIntegral (1 / 2 - σ) (1 / 2 - σ)‖) := by
  exact ⟨betaKernel_gamma_identity s z hd,
    fun σ hσ hσ' hs hz => betaKernel_vertical_bound s z σ hs hz⟩

end ConditionalGoldbach
