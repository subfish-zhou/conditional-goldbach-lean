module

public import ConditionalGoldbach.Proofs.CharacterTraceBounds

/-! The arithmetic positive-trace construction on every positive Hardy strip. -/
public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma characterHardyFunction_representation_on_strip (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) {a : ℝ} (ha0 : 0 < a) (ha : a < beta)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) :
    ∃ g : HardySpace (a) beta,
      (∀ s ∈ strip (a) beta, fourierLaplace g s = characterHardyFunction χ s) ∧
      ((boundaryTraces ha g).1 =ᵐ[volume] fun t => characterHardyFunction χ (line (a) t)) ∧
      ((boundaryTraces ha g).2 =ᵐ[volume] fun t => characterHardyFunction χ (line beta t)) := by
  obtain ⟨L, hLp, hbound⟩ := logDerivative_uniform_bound a beta ha0 ha.le
  have hL := hLp.le
  have hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc a beta →
      ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2 := by
    intro χ hχ s hs
    have hh := hbound N inferInstance hN4 hGRH χ
      (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2) s.re hs s.im
    have he : line s.re s.im = s := by apply Complex.ext <;> simp [line]
    simpa only [he] using hh
  let A : ℝ := L * (64 * (2 * N) ^ (1 / 4 : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hd (s : ℂ) (hs : s.re ∈ Icc (a) beta) :=
    characterHardyFunction_differentiableAt hGRH χ hχ (ha0.trans_le hs.1)
  apply hardy_column_of_closedStrip_majorant ha
    (fun s hs => (hd s ⟨hs.1.le, hs.2.le⟩).differentiableWithinAt)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (hardy_decay_integrable.const_mul (4 * A ^ 2))
  intro x hx t
  apply weighted_line_square_bound (ha0.le.trans hx.1) t A hA
  have hx' : (line x t).re ∈ Icc (a) beta := by simpa [line] using hx
  have hh := hlog χ hχ (line x t) hx'
  simp only [line, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at hh
  apply hh.trans
  calc
    L * Real.log (N * (|t| + 2)) ^ 2 ≤
        L * ((64 * (2 * N) ^ (1 / 4 : ℝ)) * (1 + |t|) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hN1 t) hL
    _ = A * (1 + |t|) ^ (1 / 4 : ℝ) := by dsimp [A]; ring

lemma arithmeticOperator_positive_trace_formula_on_strip (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) {a : ℝ} (ha0 : 0 < a) (ha : a < beta) :
    IsPositiveTraceClass (arithmeticOperator ha N) ∧
      positiveTrace (arithmeticOperator ha N) =
        (2 / N.totient : ℝ) * ∑ χ ∈ oddCharacters N,
          ((∫ t : ℝ, ‖characterHardyFunction χ (line (a) t)‖ ^ 2) +
            ∫ t : ℝ, ‖characterHardyFunction χ (line beta t)‖ ^ 2) := by
  classical
  let ι := {χ : Character N // χ ∈ oddCharacters N}
  have hgex (χ : ι) := characterHardyFunction_representation_on_strip N hN4 hGRH ha0 ha χ.val χ.property
  choose g hg hgl hgr using hgex
  let c : ℝ := 2 / N.totient
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let v : ι → HardySpace (a) beta := fun χ => (Real.sqrt c : ℂ) • g χ
  let f : ι → ℂ → ℂ := fun χ s => (Real.sqrt c : ℂ) * characterHardyFunction χ.val s
  have hvf (χ : ι) (s : ℂ) (hs : s ∈ strip (a) beta) : fourierLaplace (v χ) s = f χ s := by
    dsimp only [v]
    rw [fourierLaplace_smul _ _ hs, hg χ s hs]
  have hvl (χ : ι) : (boundaryTraces ha (v χ)).1 =ᵐ[volume] fun t => f χ (line (a) t) := by
    dsimp only [v]
    rw [boundaryTraces_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt c : ℂ) (boundaryTraces ha (g χ)).1, hgl χ] with t ht hg
    change ((Real.sqrt c : ℂ) • (boundaryTraces ha (g χ)).1) t = _
    rw [ht, Pi.smul_apply, smul_eq_mul, hg]
  have hvr (χ : ι) : (boundaryTraces ha (v χ)).2 =ᵐ[volume] fun t => f χ (line beta t) := by
    dsimp only [v]
    rw [boundaryTraces_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt c : ℂ) (boundaryTraces ha (g χ)).2, hgr χ] with t ht hg
    change ((Real.sqrt c : ℂ) • (boundaryTraces ha (g χ)).2) t = _
    rw [ht, Pi.smul_apply, smul_eq_mul, hg]
  have hc_cast : (c : ℂ) = (2 : ℂ) / N.totient := by dsimp [c]; push_cast; rfl
  have hc_sq : (Real.sqrt c : ℂ) ^ 2 = (c : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hc]
  have hgram (s z : ℂ) : weightedAnalyticKernel (characterKernel N) s z = ∑ χ : ι, f χ s * conj (f χ z) := by
    dsimp only [f, weightedAnalyticKernel, characterHardyFunction]
    rw [Finset.sum_coe_sort (oddCharacters N) (fun χ : Character N =>
      (Real.sqrt c : ℂ) * (logDerivative χ s / (1 + s)) *
        conj ((Real.sqrt c : ℂ) * (logDerivative χ z / (1 + z))))]
    simp only [characterKernel, Complex.conj_conj]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [map_mul, Complex.conj_ofReal, map_div₀, map_add, map_one]
    calc
      (2 / (N.totient : ℂ) * (logDerivative χ s * conj (logDerivative χ z))) /
          ((1 + s) * (1 + conj z)) =
        (Real.sqrt c : ℂ) ^ 2 * (logDerivative χ s / (1 + s)) *
          (conj (logDerivative χ z) / (1 + conj z)) := by
          rw [hc_sq, hc_cast]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
      _ = _ := by ring
  have hrep := hardyFiniteGram_represents ha N v f (weightedAnalyticKernel (characterKernel N)) hvf hvl hvr hgram
  have he : arithmeticOperator ha N = ∑ χ : ι, rankOne ℂ (v χ) (v χ) :=
    kernelOperator_eq_of_represents ha N hrep
  have ht := rankOne_tsum_positiveTraceClass v (hasSum_fintype (fun χ : ι => ‖v χ‖ ^ 2)).summable
    (Classical.choice (hardySpace_exists_nat_hilbertBasis (a) beta))
  rw [tsum_fintype, tsum_fintype] at ht
  refine ⟨he ▸ ht.1, ?_⟩
  rw [he, ht.2]
  have hnorm (χ : ι) : ‖v χ‖ ^ 2 = c *
      ((∫ t : ℝ, ‖characterHardyFunction χ.val (line (a) t)‖ ^ 2) +
        ∫ t : ℝ, ‖characterHardyFunction χ.val (line beta t)‖ ^ 2) := by
    dsimp only [v]
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hc, boundaryTraces_norm_sq ha (g χ),
      l2_norm_sq_integral, l2_norm_sq_integral]
    congr 1
    apply congrArg₂ (· + ·)
    · exact integral_congr_ae ((hgl χ).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    · exact integral_congr_ae ((hgr χ).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  simp_rw [hnorm]
  rw [← Finset.mul_sum, Finset.sum_coe_sort (oddCharacters N) (fun χ : Character N =>
    (∫ t : ℝ, ‖characterHardyFunction χ (line (a) t)‖ ^ 2) +
      ∫ t : ℝ, ‖characterHardyFunction χ (line beta t)‖ ^ 2)]

lemma arithmeticOperator_trace_le_averages_on_strip (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) {a : ℝ} (ha0 : 0 < a) (ha : a < beta) :
    IsPositiveTraceClass (arithmeticOperator ha N) ∧
      hsNorm (arithmeticOperator ha N) ≤ positiveTrace (arithmeticOperator ha N) ∧
      positiveTrace (arithmeticOperator ha N) ≤
        averagedLogDerivative N (a) + averagedLogDerivative N beta := by
  obtain ⟨hp, htrace⟩ := arithmeticOperator_positive_trace_formula_on_strip N hN4 hGRH ha0 ha
  refine ⟨hp, hp.hsNorm_le_trace, ?_⟩
  rw [htrace, averagedLogDerivative, averagedLogDerivative, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro χ hχ
  exact add_le_add
    (characterHardyFunction_energy_le N hN4 hGRH χ hχ (a) ha0)
    (characterHardyFunction_energy_le N hN4 hGRH χ hχ beta (by norm_num [beta]))

lemma arithmeticOperator_trace_bound_of_average_on_strip (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) {a : ℝ} (ha0 : 0 < a) (ha : a < beta)
    (C : ℝ) (hC : 0 ≤ C)
    (haverage : ∀ σ : ℝ, 0 < σ → σ ≤ beta →
      averagedLogDerivative N σ ≤ C * (Real.log N ^ 2 + σ⁻¹ ^ 2)) :
    IsPositiveTraceClass (arithmeticOperator ha N) ∧
      hsNorm (arithmeticOperator ha N) ≤ positiveTrace (arithmeticOperator ha N) ∧
      positiveTrace (arithmeticOperator ha N) ≤ 2 * C * (Real.log N ^ 2 + (a)⁻¹ ^ 2) := by
  obtain ⟨hp, hhs, hb⟩ := arithmeticOperator_trace_le_averages_on_strip N hN4 hGRH ha0 ha
  refine ⟨hp, hhs, hb.trans ?_⟩
  have hi : beta⁻¹ ≤ (a)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha0 ha.le
  have hisq := (sq_le_sq₀ (by norm_num [beta] : (0 : ℝ) ≤ beta⁻¹) (by positivity)).mpr hi
  have hA := haverage (a) ha0 ha.le
  have hB := haverage beta (by norm_num [beta]) le_rfl
  have hm := mul_le_mul_of_nonneg_left hisq hC
  nlinarith

end ConditionalGoldbach
