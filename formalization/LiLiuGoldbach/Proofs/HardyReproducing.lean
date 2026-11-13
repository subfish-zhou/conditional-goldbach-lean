import LiLiuGoldbach.Proofs.HardyEvaluation
import LiLiuGoldbach.Proofs.BetaIntegrals

/-! Exact evaluation of the strip reproducing kernel, including its normalization. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace LiLiuGoldbach16

lemma euler_reflection_integral {v : ℂ} (hv : 0 < v.re) (hv' : v.re < 1) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (v - 1) / (1 + t)) =
      (Real.pi : ℂ) / Complex.sin (Real.pi * v) := by
  have he1 : (-1 / 2 - (1 / 2 - v) : ℂ) = v - 1 := by ring
  have he2 : (-1 / 2 - (1 / 2 : ℂ)) = -1 := by ring
  have he3 : (1 / 2 - (1 / 2 - v) : ℂ) = v := by ring
  have he4 : (1 / 2 - v + (1 / 2 : ℂ)) = 1 - v := by ring
  have hi := beta_difference_integral 1 (by norm_num) (1 / 2 - v) (1 / 2)
  simp only [he1, he2, he3, he4, Complex.ofReal_one, Complex.one_cpow, one_mul,
    Complex.cpow_neg_one, ← div_eq_mul_inv] at hi
  have hi' : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (v - 1) / (1 + t)) =
      betaIntegral v (1 - v) := by
    convert hi using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [add_comm (1 : ℂ)]
  rw [hi', Complex.betaIntegral_eq_Gamma_mul_div v (1 - v) hv (by simp; linarith),
    add_sub_cancel, Complex.Gamma_one, div_one, Complex.Gamma_mul_Gamma_one_sub]

lemma exp_logistic_substitution (v : ℂ) (x : ℝ) :
    Real.exp x • (((Real.exp x : ℝ) : ℂ) ^ (v - 1) / (1 + Real.exp x)) =
      Complex.exp (v * x) / (1 + Real.exp x) := by
  rw [Complex.real_smul, ← mul_div_assoc]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring

lemma exp_logistic_integral {v : ℂ} (hv : 0 < v.re) (hv' : v.re < 1) :
    (∫ x : ℝ, Complex.exp (v * x) / (1 + Real.exp x)) =
      (Real.pi : ℂ) / Complex.sin (Real.pi * v) := by
  rw [← euler_reflection_integral hv hv', ← integral_comp_exp]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (exp_logistic_substitution v x).symm)

lemma hardy_evaluation_integrand_scale (a b : ℝ) (u : ℂ) (τ : ℝ) (hab : a < b) :
    Complex.exp (u * τ) / (hardyWeight a b τ : ℂ) =
      Complex.exp (((u - 2 * a) / (2 * (b - a : ℝ))) * ((2 * (b - a) * τ : ℝ) : ℂ)) /
        (1 + Real.exp (2 * (b - a) * τ)) := by
  have hd : (2 * (b - a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 2 * (b - a) ≠ 0 by linarith)
  have he : ((u - 2 * a) / (2 * (b - a : ℝ))) * ((2 * (b - a) * τ : ℝ) : ℂ) =
      u * τ - (2 * a * τ : ℝ) := by
    have hba : (b : ℂ) - a ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hab.ne.symm)
    push_cast
    field_simp
  rw [he, Complex.exp_sub]
  have ha : (Real.exp (2 * a * τ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hw : (hardyWeight a b τ : ℂ) =
      (Real.exp (2 * a * τ) : ℂ) * (1 + Real.exp (2 * (b - a) * τ)) := by
    unfold hardyWeight
    push_cast
    rw [mul_add, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [hw, ← Complex.ofReal_exp, div_div]

lemma hardy_evaluation_integral {a b : ℝ} (hab : a < b) (u : ℂ)
    (hu : 2 * a < u.re) (hu' : u.re < 2 * b) :
    (∫ τ : ℝ, Complex.exp (u * τ) / (hardyWeight a b τ : ℂ)) =
      (2 * (b - a : ℝ) : ℂ)⁻¹ *
        ((Real.pi : ℂ) / Complex.sin (Real.pi * ((u - 2 * a) / (2 * (b - a : ℝ))))) := by
  let v : ℂ := (u - 2 * a) / (2 * (b - a : ℝ))
  have hd : 0 < 2 * (b - a) := by linarith
  have hre : v.re = (u.re - 2 * a) / (2 * (b - a)) := by
    dsimp [v]
    have hc : (2 : ℂ) * ((b - a : ℝ) : ℂ) = ((2 * (b - a) : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.div_ofReal_re]
    simp
  have hv : 0 < v.re := by rw [hre]; exact div_pos (by linarith) hd
  have hv' : v.re < 1 := by rw [hre]; exact (div_lt_one hd).mpr (by linarith)
  calc
    _ = ∫ τ : ℝ, Complex.exp (v * ((2 * (b - a) * τ : ℝ) : ℂ)) /
        (1 + Real.exp (2 * (b - a) * τ)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun τ => hardy_evaluation_integrand_scale a b u τ hab)
    _ = |(2 * (b - a))⁻¹| • ∫ x : ℝ, Complex.exp (v * x) / (1 + Real.exp x) :=
      Measure.integral_comp_mul_left
        (fun x : ℝ => Complex.exp (v * x) / (1 + Real.exp x)) (2 * (b - a))
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr hd), exp_logistic_integral hv hv', Complex.real_smul,
        Complex.ofReal_inv]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, v]

lemma evaluationVector_reproducingKernel {a b : ℝ} (hab : a < b) {s z : ℂ}
    (hs : s ∈ strip a b) (hz : z ∈ strip a b) :
    fourierLaplace (evaluationVector z : HardySpace a b) s = reproducingKernel a b s z := by
  have hu : 2 * a < (s + conj z).re := by
    simp only [Complex.add_re, Complex.conj_re]
    linarith [hs.1, hz.1]
  have hu' : (s + conj z).re < 2 * b := by
    simp only [Complex.add_re, Complex.conj_re]
    linarith [hs.2, hz.2]
  rw [evaluationVector_fourierLaplace_integral hs hz, hardy_evaluation_integral hab _ hu hu']
  unfold reproducingKernel
  have hc : (2 * Real.pi : ℂ)⁻¹ * (2 * (b - a : ℝ) : ℂ)⁻¹ * Real.pi =
      (4 * (b - a : ℝ) : ℂ)⁻¹ := by
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hd : ((b - a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hab.ne.symm)
    field_simp
    <;> ring
  rw [← mul_assoc, ← mul_div_assoc, hc]
  congr 2
  ring

lemma reproducingKernel_diag {a b : ℝ} (hab : a < b) (s : ℂ) :
    reproducingKernel a b s s =
      ((1 / (4 * (b - a) * Real.sin (Real.pi * (s.re - a) / (b - a))) : ℝ) : ℂ) := by
  have hs : s + conj s = (2 * s.re : ℝ) := by apply Complex.ext <;> simp <;> ring
  unfold reproducingKernel
  rw [hs]
  have he : (Real.pi : ℂ) * ((2 * s.re : ℝ) - 2 * a) / (2 * (b - a : ℝ)) =
      ((Real.pi * (s.re - a) / (b - a) : ℝ) : ℂ) := by
    have hd : (b : ℂ) - a ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hab.ne.symm)
    push_cast
    field_simp
    <;> ring
  rw [he, ← Complex.ofReal_sin]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_inv, one_mul, one_div, mul_inv, div_eq_mul_inv]

theorem proposition_5_4_exact_norm (a b : ℝ) (hab : a < b)
    (s : ℂ) (hs : s ∈ strip a b) :
    ‖(evaluationVector s : HardySpace a b)‖ ^ 2 =
      1 / (4 * (b - a) * Real.sin (Real.pi * (s.re - a) / (b - a))) := by
  have hv : (fourierLaplace (evaluationVector s : HardySpace a b) s).re =
      ‖(evaluationVector s : HardySpace a b)‖ ^ 2 := by
    rw [evaluationVector_spec hs, paperInner]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (evaluationVector s : HardySpace a b)
  rw [← hv, evaluationVector_reproducingKernel hab hs hs, reproducingKernel_diag hab]
  rfl

lemma sin_pi_mul_lower {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    2 * min t (1 - t) ≤ Real.sin (Real.pi * t) := by
  by_cases hhalf : t ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    convert Real.le_sin_mul (show 0 ≤ 2 * t by linarith) (show 2 * t ≤ 1 by linarith) using 1
    congr 1
    ring
  · rw [min_eq_right (by linarith)]
    have h := Real.le_sin_mul (show 0 ≤ 2 * (1 - t) by linarith)
      (show 2 * (1 - t) ≤ 1 by linarith)
    have he : Real.pi / 2 * (2 * (1 - t)) = Real.pi - Real.pi * t := by ring
    rwa [he, Real.sin_pi_sub] at h

lemma evaluationVector_norm_sq_le {a b : ℝ} (hab : a < b) {s : ℂ}
    (hs : s ∈ strip a b) :
    ‖(evaluationVector s : HardySpace a b)‖ ^ 2 ≤ 1 / (8 * pointDistance a b s) := by
  rw [proposition_5_4_exact_norm a b hab s hs]
  let t : ℝ := (s.re - a) / (b - a)
  have hd : 0 < b - a := sub_pos.mpr hab
  have ht : 0 < t := div_pos (sub_pos.mpr hs.1) hd
  have ht' : t < 1 := (div_lt_one hd).mpr (by linarith [hs.2])
  have hsine := sin_pi_mul_lower ht.le ht'.le
  have hdist : pointDistance a b s = (b - a) * min t (1 - t) := by
    rw [mul_min_of_nonneg _ _ hd.le]
    unfold pointDistance
    congr 1 <;> dsimp [t] <;> field_simp <;> ring
  have hp : 0 < pointDistance a b s := lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)
  have hden : 8 * pointDistance a b s ≤
      4 * (b - a) * Real.sin (Real.pi * (s.re - a) / (b - a)) := by
    rw [hdist]
    have h := mul_le_mul_of_nonneg_left hsine (show 0 ≤ 4 * (b - a) by positivity)
    dsimp [t] at h
    rw [← mul_div_assoc] at h
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) hden

lemma evaluationVector_norm_product_le {a b : ℝ} (hab : a < b) {s z : ℂ}
    (hs : s ∈ strip a b) (hz : z ∈ strip a b) :
    ‖(evaluationVector s : HardySpace a b)‖ * ‖(evaluationVector z : HardySpace a b)‖ ≤
      1 / (8 * Real.sqrt (pointDistance a b s * pointDistance a b z)) := by
  have hds : 0 < pointDistance a b s := lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)
  have hdz : 0 < pointDistance a b z := lt_min (sub_pos.mpr hz.1) (sub_pos.mpr hz.2)
  have hn := mul_le_mul (evaluationVector_norm_sq_le hab hs) (evaluationVector_norm_sq_le hab hz)
    (sq_nonneg _) (by positivity : 0 ≤ 1 / (8 * pointDistance a b s))
  have hr := Real.sqrt_le_sqrt hn
  rw [← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at hr
  calc
    _ ≤ Real.sqrt ((1 / (8 * pointDistance a b s)) * (1 / (8 * pointDistance a b z))) := hr
    _ = _ := by
      have he : (1 / (8 * pointDistance a b s)) * (1 / (8 * pointDistance a b z)) =
          1 / ((8 : ℝ) ^ 2 * (pointDistance a b s * pointDistance a b z)) := by ring
      rw [he, Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]

end LiLiuGoldbach16
