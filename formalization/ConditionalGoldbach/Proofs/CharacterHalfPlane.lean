module

public import ConditionalGoldbach.Proofs.HalfPlaneWeightedCauchy
public import ConditionalGoldbach.Proofs.CharacterReferenceEnergy

/-! The half-plane weighted real-part estimate for actual logarithmic derivatives. -/
public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma logDerivative_right_bound (N : ℕ) [NeZero N] (χ : Character N)
    (s : ℂ) (hs : 1 ≤ s.re) : ‖logDerivative χ s‖ ≤ 3 * (Real.log 4 + 4) := by
  have hs' : 1 / 2 < s.re := by linarith
  have hsum := summable_logDerivative_terms χ hs'
  have hshift := (summable_nat_add_iff 1).mpr hsum
  have hm := mangoldt_positive_series_bound (1/2) (by norm_num)
  rw [logDerivative_eq_neg_tsum χ hs', norm_neg, hsum.tsum_eq_zero_add]
  simp only [mangoldt, ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, zero_div, zero_add]
  apply (norm_tsum_le_tsum_norm hshift.norm).trans
  apply (Summable.tsum_le_tsum _ hshift.norm hm.1).trans
  · convert hm.2 using 1; norm_num; ring
  intro j
  have hn : 0 < (j+1 : ℕ) := by omega
  have hn1 : (1 : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast hn
  have hΛ : 0 ≤ mangoldt (j+1) := ArithmeticFunction.vonMangoldt_nonneg
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ,
    Complex.norm_natCast_cpow_of_pos hn]
  have hnum : mangoldt (j+1) * ‖χ ((j+1 : ℕ) : ZMod N)‖ ≤ mangoldt (j+1) :=
    mul_le_of_le_one_right hΛ (χ.norm_le_one _)
  have hden : ((j+1 : ℕ) : ℝ) ^ (1+(1/2 : ℝ)) ≤ ((j+1 : ℕ) : ℝ) ^ (1/2+s).re := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    norm_num [Complex.add_re]
    linarith
  exact (div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (by positivity) _)).trans
    (div_le_div_of_nonneg_left hΛ (Real.rpow_pos_of_pos (by positivity) _) hden)

lemma shifted_logDerivative_holomorphic (N : ℕ) [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) {σ : ℝ} (hσ : 0 < σ) :
    ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ (fun z => logDerivative χ ((σ : ℂ) + z)) z := by
  intro z hz
  have ha := odd_logDerivative_analyticAt_of_GRH hGRH χ hχ (s := (σ : ℂ)+z)
    (by simp only [add_re, ofReal_re]; linarith)
  exact ha.differentiableAt.comp z (differentiableAt_id.const_add (σ : ℂ))

lemma shifted_logDerivative_growth (N : ℕ) [NeZero N] (hN4 : 4 ≤ N) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) {σ : ℝ} (hσ : 0 < σ) :
    ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖logDerivative χ ((σ : ℂ) + line x t)‖ ≤ C * (1 + |t|) ^ (1/4 : ℝ) := by
  intro R hR
  obtain ⟨L,hL,hb⟩ := logDerivative_uniform_bound σ (σ+R) hσ (by linarith)
  refine ⟨L * (64 * (2*N) ^ (1/4 : ℝ)), by positivity, ?_⟩
  intro x hx t
  have hh := hb N inferInstance hN4 hGRH χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2)
    (σ+x) ⟨by linarith [hx.1], by linarith [hx.2]⟩ t
  have he : (σ : ℂ) + line x t = line (σ+x) t := by unfold line; push_cast; ring
  rw [he]
  apply hh.trans
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  convert mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hn1 t) hL.le using 1; ring

lemma logDerivative_weighted_realPart_bound (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun t : ℝ => (logDerivative χ (line σ t)).re ^ 2 / (1+t^2)) ∧
      (∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1+t^2)) ≤
        2 * (∫ t : ℝ, (logDerivative χ (line σ t)).re ^ 2 / (1+t^2)) +
          Real.pi * (3 * (Real.log 4 + 4)) ^ 2 := by
  have he (t : ℝ) : (σ : ℂ)+line 0 t = line σ t := by simp [line]
  have hh := halfPlane_weighted_realPart (fun z => logDerivative χ ((σ : ℂ)+z))
    (shifted_logDerivative_holomorphic N hGRH χ hχ hσ)
    (shifted_logDerivative_growth N hN4 hGRH χ hχ hσ)
    (by
      refine ⟨1, 3*(Real.log 4+4), by positivity, ?_⟩
      intro z hz
      exact logDerivative_right_bound N χ _ (by simp only [add_re, ofReal_re]; linarith))
    (by simpa only [he] using logDerivative_weighted_square_integrable N hN4 hGRH χ hχ σ hσ)
  simp only [he] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (logDerivative_right_bound N χ ((σ : ℂ)+1) (by simp only [add_re, ofReal_re, one_re]; linarith))

end ConditionalGoldbach
