import LiLiuGoldbach.Proofs.MellinBasic

/-! Integration by parts for the compact Mellin test functions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

def mellinD (f : ℝ → ℝ) (u : ℝ) : ℝ := f u - u * deriv f u

lemma mellinD_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (mellinD f) := by
  exact hf.sub (contDiff_id.mul (contDiff_infty_iff_deriv.mp hf).2)

lemma mellinD_support {f : ℝ → ℝ}
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) :
    Function.support (mellinD f) ⊆ Icc (1 / 3 : ℝ) (2 / 3) := by
  have ht : tsupport f ⊆ Icc (1 / 3 : ℝ) (2 / 3) := closure_minimal hs isClosed_Icc
  intro x hx
  by_contra hout
  have hz : f x = 0 := by by_contra hn; exact hout (hs hn)
  have hdz : deriv f x = 0 := by by_contra hn; exact hout (ht (support_deriv_subset hn))
  exact hx (by simp [mellinD, hz, hdz])

lemma mellin_test_interval (f : ℝ → ℝ)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (s : ℂ) :
    mellin (fun u => (f u : ℂ)) s =
      ∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ), (u : ℂ) ^ (s - 1) * (f u : ℂ) := by
  have hsupport : Function.support (fun u : ℝ => (u : ℂ) ^ (s - 1) * (f u : ℂ)) ⊆
      Ioc (1 / 4 : ℝ) (3 / 4) := by
    intro u hu
    have hn : f u ≠ 0 := by intro hzero; exact hu (by simp [hzero])
    have h := hs hn
    constructor <;> linarith [h.1, h.2]
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  unfold mellin
  simp only [smul_eq_mul]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have hf0 : f u = 0 := by
    by_contra hn
    have h := hs hn
    simp only [mem_Ioi, not_lt] at hu
    linarith [h.1]
  simp [hf0]

lemma mellin_test_intervalIntegrable (f : ℝ → ℝ) (hf : Continuous f) (s : ℂ) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ s * (f u : ℂ)) volume (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)] at hu
  have hu0 : u ≠ 0 := by linarith [hu.1]
  exact ((Complex.continuousAt_ofReal_cpow_const u s (Or.inr hu0)).mul
    (Complex.continuous_ofReal.continuousAt.comp hf.continuousAt)).continuousWithinAt

theorem mellinD_transform (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (s : ℂ) :
    mellin (fun u => (mellinD f u : ℂ)) s = (1 + s) * mellin (fun u => (f u : ℂ)) s := by
  let A : ℝ → ℂ := fun u => (u : ℂ) ^ (s - 1) * (f u : ℂ)
  let B : ℝ → ℂ := fun u => (u : ℂ) ^ s * ((deriv f u : ℝ) : ℂ)
  have hA : IntervalIntegrable A volume (1 / 4 : ℝ) (3 / 4 : ℝ) :=
    mellin_test_intervalIntegrable f hf.continuous (s - 1)
  have hB : IntervalIntegrable B volume (1 / 4 : ℝ) (3 / 4 : ℝ) :=
    mellin_test_intervalIntegrable (deriv f) (contDiff_infty_iff_deriv.mp hf).2.continuous s
  have hFTC : (∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ), s * A u + B u) = 0 := by
    have hd (u : ℝ) (hu : u ∈ uIcc (1 / 4 : ℝ) (3 / 4 : ℝ)) :
        HasDerivAt (fun u : ℝ => (u : ℂ) ^ s * (f u : ℂ)) (s * A u + B u) u := by
      rw [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)] at hu
      have hu0 : u ≠ 0 := by linarith [hu.1]
      have hcp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (u : ℂ) ^ (s - 1)) u := by
        by_cases hs0 : s = 0
        · subst s
          simpa using hasDerivAt_const u (1 : ℂ)
        · exact hasDerivAt_ofReal_cpow_const hu0 hs0
      convert hcp.mul ((hf.differentiable (by norm_num) u).hasDerivAt.ofReal_comp) using 1
      dsimp [A, B]
      ring
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((hA.const_mul s).add hB)
    have hz₁ : f (1 / 4 : ℝ) = 0 := by
      by_contra hn
      have h := hs hn
      norm_num at h
    have hz₂ : f (3 / 4 : ℝ) = 0 := by
      by_contra hn
      have h := hs hn
      norm_num at h
    simpa only [hz₁, hz₂, Complex.ofReal_zero, mul_zero, sub_self] using heq
  rw [intervalIntegral.integral_add (hA.const_mul s) hB,
    intervalIntegral.integral_const_mul] at hFTC
  rw [mellin_test_interval _ (mellinD_support hs), mellin_test_interval _ hs]
  have hD : (∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ), (u : ℂ) ^ (s - 1) * (mellinD f u : ℂ)) =
      ∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ), A u - B u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)] at hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hu.1])
    have hpow : (u : ℂ) ^ (s - 1) * u = (u : ℂ) ^ s := by
      calc
        _ = (u : ℂ) ^ (s - 1) * (u : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
        _ = (u : ℂ) ^ ((s - 1) + 1) := (cpow_add _ _ hu0).symm
        _ = _ := by congr 1; ring
    dsimp [A, B, mellinD]
    push_cast
    rw [mul_sub, ← mul_assoc, hpow]
  rw [hD, intervalIntegral.integral_sub hA hB]
  change (∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ), A u) - (∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ), B u) =
    (1 + s) * ∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ), A u
  linear_combination -hFTC


lemma mellinD_iterate_regular (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (k : ℕ) :
    ContDiff ℝ ∞ (mellinD^[k] f) ∧
      Function.support (mellinD^[k] f) ⊆ Icc (1 / 3 : ℝ) (2 / 3) := by
  induction k with
  | zero => exact ⟨hf, hs⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨mellinD_contDiff ih.1, mellinD_support ih.2⟩

lemma mellinD_iterate_transform (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (k : ℕ) (s : ℂ) :
    mellin (fun u => (mellinD^[k] f u : ℂ)) s =
      (1 + s) ^ k * mellin (fun u => (f u : ℂ)) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', mellinD_transform _
      (mellinD_iterate_regular f hf hs k).1 (mellinD_iterate_regular f hf hs k).2, ih, pow_succ]
    ring

lemma mellin_test_uniform_bound (f : ℝ → ℝ) (hf : Continuous f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (lo : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, lo ≤ s.re → ‖mellin (fun u => (f u : ℂ)) s‖ ≤ C := by
  let B := ∫ u in (1 / 4 : ℝ)..(3 / 4 : ℝ),
    ‖(u : ℂ) ^ ((lo : ℂ) - 1) * (f u : ℂ)‖
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => norm_nonneg _)
  refine ⟨B + 1, by positivity, fun s hsl => ?_⟩
  rw [mellin_test_interval _ hs]
  apply le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num))
  apply le_trans _ (by linarith : B ≤ B + 1)
  apply intervalIntegral.integral_mono_on (by norm_num)
    (mellin_test_intervalIntegrable f hf (s - 1)).norm
    (mellin_test_intervalIntegrable f hf ((lo : ℂ) - 1)).norm
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hu1 : u ≤ 1 := by linarith [hu.2]
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_re, ofReal_re, one_re]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by linarith))
    (norm_nonneg _)



lemma mellin_test_rapid_decay (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Icc (1 / 3 : ℝ) (2 / 3)) (lo : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, lo ≤ s.re →
      ‖mellin (fun u => (f u : ℂ)) s‖ ≤ C * (1 + |s.im|)⁻¹ ^ k := by
  obtain ⟨C₀, hC₀, hzero⟩ := mellin_test_uniform_bound f hf.continuous hs lo
  obtain ⟨Ck, hCk, hk⟩ := mellin_test_uniform_bound (mellinD^[k] f)
    (mellinD_iterate_regular f hf hs k).1.continuous (mellinD_iterate_regular f hf hs k).2 lo
  refine ⟨2 ^ k * (C₀ + Ck), by positivity, fun s hsl => ?_⟩
  have hnorm := hk s hsl
  rw [mellinD_iterate_transform f hf hs k s, norm_mul, norm_pow] at hnorm
  have him : |s.im| ≤ ‖1 + s‖ := by simpa only [add_im, one_im, zero_add] using Complex.abs_im_le_norm (1 + s)
  have hpower : |s.im| ^ k * ‖mellin (fun u => (f u : ℂ)) s‖ ≤ Ck :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) him k) (norm_nonneg _)).trans hnorm
  have hden : 0 < (1 + |s.im|) ^ k := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hden]
  by_cases hsmall : |s.im| ≤ 1
  · have hpow : (1 + |s.im|) ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      _ ≤ C₀ * (2 : ℝ) ^ k := mul_le_mul (hzero s hsl) hpow (by positivity) hC₀.le
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ k by positivity) hCk.le]
  · have hlarge : 1 < |s.im| := lt_of_not_ge hsmall
    have hpow : (1 + |s.im|) ^ k ≤ (2 * |s.im|) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      _ ≤ ‖mellin (fun u => (f u : ℂ)) s‖ * (2 * |s.im|) ^ k :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (2 : ℝ) ^ k * (|s.im| ^ k * ‖mellin (fun u => (f u : ℂ)) s‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ k * Ck := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem mellinWeight_uniform_decay (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (lo hi : ℝ) (hlohi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      ‖mellinWeight φ (line σ t)‖ ≤ C * (1 + |t|)⁻¹ ^ 6 := by
  obtain ⟨C, hC, hb⟩ := mellin_test_rapid_decay (companion φ)
    (companion_contDiff hφ) (companion_support_subset hφ) lo 6
  refine ⟨C, hC, fun σ hσ t => ?_⟩
  simpa only [mellinWeight, line, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, add_im, mul_im, mul_one, zero_add]
    using hb (line σ t) (by simpa [line] using hσ.1)


theorem derivativeWeight_mellin (φ : ℝ → ℝ) (hφ : IsWeight φ) (s : ℂ) :
    mellin (fun u => (derivativeWeight φ u : ℂ)) s = (1 + s) * mellinWeight φ s := by
  exact mellinD_transform (companion φ) (companion_contDiff hφ) (companion_support_subset hφ) s

end LiLiuGoldbach16
