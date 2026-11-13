import LiLiuGoldbach.Proofs.SpectralModelEuler
import LiLiuGoldbach.Proofs.SpectralModelBound
import LiLiuGoldbach.Proofs.ZetaTruncation

/-! Uniform model-kernel growth as the left Hardy boundary tends to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma riemannZeta_euler_norm_bound {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  rw [riemannZeta_fraction_formula hs hs1]
  calc
    _ ≤ ‖s / (s - 1)‖ + ‖s * zetaFractionIntegral s‖ := norm_sub_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
      rw [norm_div, norm_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (zetaFractionIntegral_norm hs) (norm_nonneg s))
    _ = _ := by ring

lemma riemannZeta_right_pole_bound (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ‖riemannZeta ((1 + σ : ℝ) : ℂ)‖ ≤ 3 / σ := by
  have hs : 0 < (((1 + σ : ℝ) : ℂ)).re := by simp; linarith
  have hs1 : ((1 + σ : ℝ) : ℂ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hh := riemannZeta_euler_norm_bound hs hs1
  have hnorm : ‖((1 + σ : ℝ) : ℂ)‖ = 1 + σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hden : ‖((1 + σ : ℝ) : ℂ) - 1‖ = σ := by
    rw [show ((1 + σ : ℝ) : ℂ) - 1 = (σ : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
  simp only [hnorm, hden, Complex.ofReal_re, div_self (show 1 + σ ≠ 0 by linarith)] at hh
  apply hh.trans
  rw [le_div_iff₀ hσ]
  field_simp
  linarith

lemma riemannZeta_left_pole_bound {s : ℂ} (hs : 3 / 4 ≤ s.re) (hs1 : s.re < 1) :
    ‖riemannZeta s‖ ≤ (8 / (1 - s.re)) * (1 + |s.im|) ^ (1 / 4 : ℝ) := by
  have hσ : 0 < 1 - s.re := by linarith
  have hp : 1 ≤ (1 + |s.im|) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by norm_num)
  by_cases ht : 1 ≤ |s.im|
  · have hh := riemannZeta_three_quarter_growth (hi := 1) hs hs1.le ht
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [le_div_iff₀ hσ]
    nlinarith
  · have hs0 : 0 < s.re := by linarith
    have hsne : s ≠ 1 := by intro he; norm_num [he] at hs1
    have hnorm : ‖s‖ ≤ 2 := by
      have hh := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hs0] at hh
      linarith
    have hden : 1 - s.re ≤ ‖s - 1‖ := by
      have hh := Complex.abs_re_le_norm (s - 1)
      simpa only [Complex.sub_re, Complex.one_re, abs_of_neg (by linarith : s.re - 1 < 0), neg_sub] using hh
    have hh := riemannZeta_euler_norm_bound hs0 hsne
    calc
      _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := hh
      _ ≤ 2 / (1 - s.re) + 2 / (3 / 4 : ℝ) := by
        exact add_le_add (div_le_div₀ (by norm_num) hnorm hσ hden)
          (div_le_div₀ (by norm_num) hnorm (by norm_num) hs)
      _ ≤ 8 / (1 - s.re) := by
        apply (le_div_iff₀ hσ).mpr
        field_simp
        nlinarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp

lemma continuedModel_norm_split (N : ℕ) (hN : 0 < N) (s z : ℂ) :
    ‖continuedModel N s z‖ = (Real.pi)^(s + z).re *
      ‖(N : ℂ)^(-(s + z)) * (singularSeries N : ℂ) * densityEulerProduct N (s + z)‖ *
      ‖riemannZeta (1 - s - z)‖ * ‖gammaQuotient s‖ * ‖gammaQuotient z‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : ‖((Real.pi : ℂ) / N)^(s + z)‖ =
      (Real.pi)^(s + z).re * ‖(N : ℂ)^(-(s + z))‖ := by
    rw [show (Real.pi : ℂ) / N = ((Real.pi / (N : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos Real.pi_pos hn),
      Real.div_rpow Real.pi_pos.le hn.le, Complex.norm_natCast_cpow_of_pos hN,
      Complex.neg_re, Real.rpow_neg hn.le, div_eq_mul_inv]
  simp only [continuedModel, norm_mul, hpow]
  ring

/-- A single constant works for all moduli and all left boundaries `a > 0`. -/
theorem continuedModel_uniform_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a < beta → ∀ N : ℕ, 0 < N →
      ∀ s z : ℂ, s.re ∈ Icc a beta → z.re ∈ Icc a beta →
      ‖continuedModel N s (conj z)‖ ≤
        C * (a⁻¹)^2 * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) := by
  obtain ⟨G, hG, hGamma⟩ := gammaQuotient_uniform_nonnegative beta
    (by norm_num [beta]) (by norm_num [beta])
  refine ⟨48 * Real.pi * G^2, by positivity, ?_⟩
  intro a ha hab N hN s z hs hz
  have hσ : 0 < (s + conj z).re := by simp; linarith [hs.1, hz.1]
  have hσa : a ≤ (s + conj z).re := by simp; linarith [hs.1, hz.1]
  have hσ1 : (s + conj z).re ≤ 1 := by
    simp only [Complex.add_re, Complex.conj_re]
    dsimp [beta] at hs hz
    linarith [hs.2, hz.2]
  have hscale : ‖(N : ℂ)^(-(s + conj z)) * (singularSeries N : ℂ) *
      densityEulerProduct N (s + conj z)‖ ≤ 6 / a := by
    calc
      _ ≤ 2 * ‖riemannZeta ((1 + (s + conj z).re : ℝ) : ℂ)‖ :=
        singularSeries_densityEuler_scaled_bound N hN hσ
      _ ≤ 2 * (3 / (s + conj z).re) :=
        mul_le_mul_of_nonneg_left (riemannZeta_right_pole_bound _ hσ hσ1) (by norm_num)
      _ ≤ 2 * (3 / a) := by gcongr
      _ = _ := by ring
  have hpi : Real.pi^(s + conj z).re ≤ Real.pi := by
    calc
      _ ≤ Real.pi^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hσ1
      _ = _ := Real.rpow_one _
  have hζ : ‖riemannZeta (1 - s - conj z)‖ ≤
      (8 / a) * ((1 + |s.im|)^(1 / 4 : ℝ) * (1 + |z.im|)^(1 / 4 : ℝ)) := by
    have hlo : 3 / 4 ≤ (1 - s - conj z).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      dsimp [beta] at hs hz
      linarith [hs.2, hz.2]
    have hhi : (1 - s - conj z).re < 1 := by simp; linarith [hs.1, hz.1]
    have hden : 1 - (1 - s - conj z).re = (s + conj z).re := by simp; ring
    have hh := riemannZeta_left_pole_bound hlo hhi
    rw [hden] at hh
    apply hh.trans
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by norm_num) ha hσa
    · rw [← Real.mul_rpow (by positivity) (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      have him : (1 - s - conj z).im = -(s.im - z.im) := by simp; ring
      rw [him, abs_neg]
      nlinarith [abs_sub s.im z.im, mul_nonneg (abs_nonneg s.im) (abs_nonneg z.im)]
    · positivity
    · positivity
  have hGs := hGamma s ⟨ha.le.trans hs.1, hs.2⟩
  have hGz := hGamma (conj z) ⟨by simpa using ha.le.trans hz.1, by simpa using hz.2⟩
  rw [continuedModel_norm_split N hN]
  calc
    _ ≤ Real.pi * (6 / a) *
        ((8 / a) * ((1 + |s.im|)^(1 / 4 : ℝ) * (1 + |z.im|)^(1 / 4 : ℝ))) * G * G := by
      gcongr
    _ = _ := by simp only [div_eq_mul_inv]; ring

end LiLiuGoldbach16
