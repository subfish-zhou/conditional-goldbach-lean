import LiLiuGoldbach.Proofs.CharacterGramOperator

/-! Comparison of the arithmetic trace with the two averaged logarithmic-derivative energies. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16

lemma norm_one_add_line_sq (x t : ℝ) : ‖1 + line x t‖ ^ 2 = (1 + x) ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [line, Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.add_im, Complex.one_im, Complex.mul_im, mul_one, zero_add]
  ring

lemma logDerivative_weighted_square_integrable (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun t : ℝ => ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2)) := by
  obtain ⟨L, hL, hb⟩ := logDerivative_uniform_bound σ σ hσ le_rfl
  have hlog := hb N inferInstance hN4 hGRH χ
    (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2) σ ⟨le_rfl, le_rfl⟩
  let A : ℝ := L * (64 * (2 * N) ^ (1 / 4 : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hct : Continuous (fun t : ℝ => logDerivative χ (line σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (odd_logDerivative_analyticAt_of_GRH hGRH χ hχ (by simpa [line] using hσ)).continuousAt.comp
      (show ContinuousAt (fun t : ℝ => line σ t) t by unfold line; fun_prop)
  have hm : AEStronglyMeasurable (fun t : ℝ => ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2)) volume :=
    ((hct.norm.pow 2).div (by fun_prop) (by intro t; positivity)).aestronglyMeasurable
  apply (hardy_decay_integrable.const_mul (4 * A ^ 2)).mono' hm
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hv : ‖logDerivative χ (line σ t)‖ ≤ A * (1 + |t|) ^ (1 / 4 : ℝ) := by
    apply (hlog t).trans
    calc
      _ ≤ L * ((64 * (2 * N) ^ (1 / 4 : ℝ)) * (1 + |t|) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hN1 t) hL.le
      _ = _ := by dsimp [A]; ring
  have hh := weighted_line_square_bound (by norm_num : (0 : ℝ) ≤ 0) t A hA _ hv
  simpa only [norm_div, div_pow, norm_one_add_line_sq, add_zero, one_pow] using hh

lemma characterHardyFunction_energy_le (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    (σ : ℝ) (hσ : 0 < σ) :
    (∫ t : ℝ, ‖characterHardyFunction χ (line σ t)‖ ^ 2) ≤
      ∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2) := by
  have hi := logDerivative_weighted_square_integrable N hN4 hGRH χ hχ σ hσ
  have hbound (t : ℝ) : ‖characterHardyFunction χ (line σ t)‖ ^ 2 ≤
      ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2) := by
    rw [characterHardyFunction, norm_div, div_pow, norm_one_add_line_sq]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg σ]
  have hc : Continuous (fun t : ℝ => characterHardyFunction χ (line σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (characterHardyFunction_differentiableAt hGRH χ hχ (by simpa [line] using hσ)).continuousAt.comp
      (show ContinuousAt (fun t : ℝ => line σ t) t by unfold line; fun_prop)
  have hil : Integrable (fun t : ℝ => ‖characterHardyFunction χ (line σ t)‖ ^ 2) := by
    apply hi.mono' (hc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with t
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using hbound t
  exact integral_mono hil hi hbound

lemma arithmeticOperator_trace_le_averages (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    IsPositiveTraceClass (arithmeticOperator ha N) ∧
      hsNorm (arithmeticOperator ha N) ≤ positiveTrace (arithmeticOperator ha N) ∧
      positiveTrace (arithmeticOperator ha N) ≤
        averagedLogDerivative N (alpha N) + averagedLogDerivative N beta := by
  obtain ⟨hp, htrace⟩ := arithmeticOperator_positive_trace_formula N hlarge hGRH ha
  refine ⟨hp, hp.hsNorm_le_trace, ?_⟩
  rw [htrace, averagedLogDerivative, averagedLogDerivative, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro χ hχ
  exact add_le_add
    (characterHardyFunction_energy_le N (large_parameters hlarge).1 hGRH χ hχ (alpha N) (large_alpha_pos hlarge))
    (characterHardyFunction_energy_le N (large_parameters hlarge).1 hGRH χ hχ beta (by norm_num [beta]))

lemma arithmeticOperator_trace_bound_of_average (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (C : ℝ) (hC : 0 ≤ C)
    (haverage : ∀ σ : ℝ, 0 < σ → σ ≤ beta →
      averagedLogDerivative N σ ≤ C * (Real.log N ^ 2 + σ⁻¹ ^ 2)) :
    IsPositiveTraceClass (arithmeticOperator ha N) ∧
      hsNorm (arithmeticOperator ha N) ≤ positiveTrace (arithmeticOperator ha N) ∧
      positiveTrace (arithmeticOperator ha N) ≤ 2 * C * (Real.log N ^ 2 + (alpha N)⁻¹ ^ 2) := by
  obtain ⟨hp, hhs, hb⟩ := arithmeticOperator_trace_le_averages N hlarge hGRH ha
  refine ⟨hp, hhs, hb.trans ?_⟩
  have ha0 := large_alpha_pos hlarge
  have hi : beta⁻¹ ≤ (alpha N)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha0 ha.le
  have hisq := (sq_le_sq₀ (by norm_num [beta] : (0 : ℝ) ≤ beta⁻¹) (by positivity)).mpr hi
  have hA := haverage (alpha N) ha0 ha.le
  have hB := haverage beta (by norm_num [beta]) le_rfl
  have hm := mul_le_mul_of_nonneg_left hisq hC
  nlinarith

end LiLiuGoldbach16
