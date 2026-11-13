import ConditionalGoldbach.Proofs.GammaQuotientBound
import ConditionalGoldbach.Proofs.SpectralPoissonConvolution

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- Taking real parts of the Beta parameters gives a sharp modulus majorant. -/
theorem betaIntegral_norm_le_real (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖betaIntegral u v‖ ≤ ‖betaIntegral (u.re : ℂ) (v.re : ℂ)‖ := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (u - 1) * (1 - (t : ℂ)) ^ (v - 1)
  have heq : ((∫ t : ℝ in 0..1, ‖F t‖ : ℝ) : ℂ) = betaIntegral (u.re : ℂ) (v.re : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have h1 : 0 < 1 - t := sub_pos.mpr ht.2
    have he : 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
    simp only [F, norm_mul, he, Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
      Complex.norm_cpow_eq_rpow_re_of_pos h1, sub_re, one_re, ofReal_mul]
    rw [show (u.re : ℂ) - 1 = ((u.re - 1 : ℝ) : ℂ) by push_cast; rfl,
      show (v.re : ℂ) - 1 = ((v.re - 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow ht.1.le, ← Complex.ofReal_cpow h1.le]
  have hn : 0 ≤ ∫ t : ℝ in 0..1, ‖F t‖ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t ht => norm_nonneg _)
  calc
    ‖betaIntegral u v‖ ≤ ∫ t : ℝ in 0..1, ‖F t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖betaIntegral (u.re : ℂ) (v.re : ℂ)‖ := by
      rw [← heq, norm_real, Real.norm_eq_abs, abs_of_nonneg hn]

/-- On a vertical line the Gamma quotient is bounded by its value on the real axis. -/
theorem gammaQuotient_norm_le_real (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 3 / 2) :
    ‖gammaQuotient s‖ ≤ ‖gammaQuotient (s.re : ℂ)‖ := by
  have hp : 0 < ((3 / 2 - conj s) / 2).re := by simp; linarith
  rw [gammaQuotient_norm_beta s hs hs',
    gammaQuotient_norm_beta (s.re : ℂ) hs hs']
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h := betaIntegral_norm_le_real ((3 / 2 - conj s) / 2) (s.re : ℂ) hp hs
  convert h using 1 <;> congr 2 <;> apply Complex.ext <;> simp <;> ring

/-- A single uniform Gamma-quotient bound remains valid down to the imaginary axis. -/
theorem gammaQuotient_uniform_nonnegative (b : ℝ) (hb0 : 0 ≤ b) (hb : b < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc 0 b → ‖gammaQuotient s‖ ≤ C := by
  have hc : ContinuousOn (fun x : ℝ => gammaQuotient (x : ℂ)) (Icc 0 b) := by
    intro x hx
    have hn : 0 < ((3 / 2 - (x : ℂ)) / 2).re := by simp; linarith [hx.2]
    have hd : 0 < ((3 / 2 + (x : ℂ)) / 2).re := by simp; linarith [hx.1]
    have hg₁ := Complex.continuousAt_Gamma ((3 / 2 - (x : ℂ)) / 2) (fun m hm => by
      have hh := congrArg Complex.re hm
      simp only [neg_re, natCast_re] at hh
      have := Nat.cast_nonneg (α := ℝ) m
      linarith)
    have hg₂ := Complex.continuousAt_Gamma ((3 / 2 + (x : ℂ)) / 2) (fun m hm => by
      have hh := congrArg Complex.re hm
      simp only [neg_re, natCast_re] at hh
      have := Nat.cast_nonneg (α := ℝ) m
      linarith)
    exact ((hg₁.comp (f := fun y : ℝ => (3 / 2 - (y : ℂ)) / 2) (by fun_prop : ContinuousAt (fun x : ℝ => (3 / 2 - (x : ℂ)) / 2) x)).div
      (hg₂.comp (f := fun y : ℝ => (3 / 2 + (y : ℂ)) / 2) (by fun_prop : ContinuousAt (fun x : ℝ => (3 / 2 + (x : ℂ)) / 2) x))
      (Complex.Gamma_ne_zero_of_re_pos hd)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs
  rcases hs.1.eq_or_lt with hzero | hpos
  · have he : (3 / 2 - s) / 2 = conj ((3 / 2 + s) / 2) := by
      simp only [map_div₀, map_add, map_ofNat]
      apply Complex.ext <;> simp <;> linarith
    have hd : Gamma ((3 / 2 + s) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [gammaQuotient, he, Complex.Gamma_conj, norm_div, norm_conj, div_self (norm_ne_zero_iff.mpr hd)]
    exact le_max_right _ _
  · exact (gammaQuotient_norm_le_real s hpos (hs.2.trans_lt hb)).trans ((hC _ hs).trans (le_max_left _ _))

end ConditionalGoldbach
