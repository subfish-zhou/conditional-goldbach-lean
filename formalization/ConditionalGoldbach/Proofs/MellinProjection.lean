module

public import ConditionalGoldbach.Proofs.MellinBasic
public import ConditionalGoldbach.Proofs.CharacterSeries

/-! Absolutely convergent interchange for weighted Mellin projections. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff FourierTransform
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

theorem mellin_inversion_hasSum {ι : Type*} [Countable ι]
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (u : ι → ℝ) (b : ι → ℂ)
    (hu : ∀ i, 0 < u i)
    (hb : Summable (fun i => ‖b i‖ * Real.rpow (u i) (-σ))) :
    HasSum (fun i => b i * (companion φ (u i) : ℂ))
      (verticalMellin σ (fun s => ∑' i, b i * mellinWeight φ s * (u i : ℂ) ^ (-s))) := by
  let F : ι → ℝ → ℂ := fun i t =>
    b i * mellinWeight φ (line σ t) * (u i : ℂ) ^ (-line σ t)
  let B : ι → ℝ → ℝ := fun i t =>
    (‖b i‖ * Real.rpow (u i) (-σ)) * ‖mellinWeight φ (line σ t)‖
  have hint (i : ι) : Integrable (F i) := by
    simpa only [F, mul_assoc] using
      (mellinWeight_inversion_integrable hφ σ (u i) (hu i)).const_mul (b i)
  have heq (i : ι) (t : ℝ) : ‖F i t‖ = B i t := by
    simp only [F, B, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp only [line, neg_re, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
    rw [Real.rpow_eq_pow]
    ring
  have hBi : Integrable (fun t => ∑' i, B i t) := by
    simp only [B, tsum_mul_right]
    exact (mellinWeight_verticalIntegrable hφ σ).norm.const_mul _
  have h := hasSum_integral_of_dominated_convergence B
    (fun i => (hint i).aestronglyMeasurable)
    (fun i => Eventually.of_forall (fun t => (heq i t).le))
    (Eventually.of_forall (fun t => hb.mul_right _)) hBi
    (Eventually.of_forall (fun t =>
      (Summable.of_norm (by simpa only [heq] using hb.mul_right ‖mellinWeight φ (line σ t)‖)).hasSum))
  have hscaled := h.mul_left ((2 * (Real.pi : ℂ))⁻¹)
  convert hscaled using 1
  · ext i
    rw [mellinWeight_inversion hφ σ (u i) (hu i)]
    simp only [verticalMellin, F, mul_assoc, integral_const_mul]
    ring
  · rfl



theorem mellin_inversion_sum_integrable {ι : Type*} [Countable ι]
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (u : ι → ℝ) (b : ι → ℂ)
    (hu : ∀ i, 0 < u i)
    (hb : Summable (fun i => ‖b i‖ * Real.rpow (u i) (-σ))) :
    Integrable (fun t : ℝ => ∑' i,
      b i * mellinWeight φ (line σ t) * (u i : ℂ) ^ (-line σ t)) := by
  let F : ι → ℝ → ℂ := fun i t =>
    b i * mellinWeight φ (line σ t) * (u i : ℂ) ^ (-line σ t)
  have hint (i : ι) : Integrable (F i) := by
    simpa only [F, mul_assoc] using
      (mellinWeight_inversion_integrable hφ σ (u i) (hu i)).const_mul (b i)
  have hnorm (i : ι) (t : ℝ) : ‖F i t‖ =
      (‖b i‖ * Real.rpow (u i) (-σ)) * ‖mellinWeight φ (line σ t)‖ := by
    simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp only [line, neg_re, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, Real.rpow_eq_pow]
    ring
  apply ((mellinWeight_verticalIntegrable hφ σ).norm.const_mul
    (∑' i, ‖b i‖ * Real.rpow (u i) (-σ))).mono'
    (AEStronglyMeasurable.tsum (fun i => (hint i).aestronglyMeasurable))
  filter_upwards [] with t
  have hs : Summable (fun i => ‖F i t‖) := by
    simpa only [hnorm] using hb.mul_right ‖mellinWeight φ (line σ t)‖
  calc
    ‖∑' i, F i t‖ ≤ ∑' i, ‖F i t‖ := norm_tsum_le_tsum_norm hs
    _ = _ := by simp only [hnorm, tsum_mul_right, line]


lemma mellin_dirichlet_rescale (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (s a : ℂ) :
    a / (n : ℂ) ^ (1 / 2 : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) ^ (-s) =
      (N : ℂ) ^ s * (a / (n : ℂ) ^ (1 / 2 + s)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hncp (z : ℂ) : (n : ℂ) ^ z ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
  rw [Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (a := (n : ℝ)) (b := (N : ℝ)) (by positivity) (by positivity),
    Complex.ofReal_natCast, Complex.ofReal_natCast, cpow_neg, cpow_neg, div_inv_eq_mul, cpow_add _ _ hn0]
  field_simp

lemma character_mellin_coeff_summable {N : ℕ} [NeZero N] (χ : Character N)
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ =>
      ‖(mangoldt (n + 1) : ℂ) * χ (n + 1) / (n + 1 : ℕ) ^ (1 / 2 : ℂ)‖ *
      Real.rpow ((n + 1 : ℕ) / (N : ℝ)) (-σ)) := by
  have hN : 0 < N := NeZero.pos _
  have hs := (summable_logDerivative_terms χ (s := (σ : ℂ)) (by simpa using hσ)).norm
  have hshift := (summable_nat_add_iff 1).2 hs
  have hnorm := hshift.mul_left ‖(N : ℂ) ^ (σ : ℂ)‖
  apply hnorm.congr
  intro n
  have hid := congrArg norm (mellin_dirichlet_rescale (n + 1) N (by omega) hN (σ : ℂ)
    ((mangoldt (n + 1) : ℂ) * χ (n + 1)))
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), norm_mul] at hid
  simpa only [neg_re, ofReal_re, Real.rpow_eq_pow, Nat.cast_add, Nat.cast_one] using hid.symm


lemma character_mellin_companion_term (N n : ℕ) (hN : 0 < N)
    (χ : Character N) (φ : ℝ → ℝ) :
    ((mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (companion φ (n / N) : ℂ) =
      (Real.sqrt N : ℂ)⁻¹ * ((mangoldt n : ℂ) * χ n * (φ (n / N) : ℂ)) := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldt]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnroot : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hnpos).ne'
  have hNroot : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hNpos).ne'
  have hhalf : (n : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (n : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hnpos.le]
    congr 1
    norm_num
  rw [hhalf]
  simp only [companion, Complex.ofReal_mul, Real.sqrt_div hnpos.le,
    Complex.ofReal_div]
  field_simp

lemma character_mellin_companion_tsum (N : ℕ) (hN : 0 < N)
    (χ : Character N) (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∑' n : ℕ, ((mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 : ℂ)) *
      (companion φ (n / N) : ℂ)) = characterPolynomial χ φ := by
  simp_rw [character_mellin_companion_term N _ hN χ φ]
  rw [tsum_mul_left]
  unfold characterPolynomial
  congr 1
  apply tsum_eq_sum
  intro n hn
  have hnlarge : N < n := by
    have : N + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    omega
  have hz : φ ((n : ℝ) / N) = 0 := by
    by_contra hnonzero
    have hs := hφ.mem_support_interval hnonzero
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hnr : (N : ℝ) < n := by exact_mod_cast hnlarge
    have hi := (div_le_iff₀ hNr).1 hs.2
    nlinarith
  simp [hz]



lemma character_mellin_series {N : ℕ} [NeZero N] (χ : Character N)
    (φ : ℝ → ℝ) (s : ℂ) (hs : 1 / 2 < s.re) :
    (∑' n : ℕ, ((mangoldt (n + 1) : ℂ) * χ (n + 1) /
      (n + 1 : ℕ) ^ (1 / 2 : ℂ)) * mellinWeight φ s *
      (((n + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-s)) =
      -((N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s) := by
  rw [logDerivative_eq_neg_tsum χ hs, mul_neg, neg_neg,
    (summable_logDerivative_terms χ hs).tsum_eq_zero_add]
  simp only [mangoldt, ArithmeticFunction.map_zero,
    Complex.ofReal_zero, zero_mul, zero_div, zero_add]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  calc
    _ = mellinWeight φ s *
        (((mangoldt (n + 1) : ℂ) * χ (n + 1) /
          (n + 1 : ℕ) ^ (1 / 2 : ℂ)) *
          (((n + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-s)) := by ring
    _ = _ := by
      rw [mellin_dirichlet_rescale (n + 1) N (by omega) (NeZero.pos _)]
      push_cast
      ring

theorem character_mellin_initial_integrable {N : ℕ} [NeZero N]
    (χ : Character N) (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 1 / 2 < σ) :
    Integrable (fun t : ℝ =>
      (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) * logDerivative χ (line σ t)) := by
  have hN : 0 < N := NeZero.pos _
  have hint := mellin_inversion_sum_integrable φ hφ σ
    (fun n : ℕ => (n + 1 : ℕ) / (N : ℝ))
    (fun n : ℕ => (mangoldt (n + 1) : ℂ) * χ (n + 1) / (n + 1 : ℕ) ^ (1 / 2 : ℂ))
    (fun n => by positivity) (character_mellin_coeff_summable χ σ hσ)
  convert hint.neg using 1
  ext t
  simp only [Pi.neg_apply]
  rw [character_mellin_series χ φ (line σ t) (by simpa [line] using hσ), neg_neg]


/-- The initial Mellin contour requires no GRH and works for every character. -/
theorem characterPolynomial_mellin_initial {N : ℕ} [NeZero N]
    (χ : Character N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    characterPolynomial χ φ = -verticalMellin σ (fun s =>
      (N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s) := by
  have hN : 0 < N := NeZero.pos _
  let u : ℕ → ℝ := fun n => (n + 1 : ℕ) / (N : ℝ)
  let b : ℕ → ℂ := fun n =>
    (mangoldt (n + 1) : ℂ) * χ (n + 1) / (n + 1 : ℕ) ^ (1 / 2 : ℂ)
  have hs := mellin_inversion_hasSum φ hφ σ u b
    (fun n => by dsimp [u]; positivity) (character_mellin_coeff_summable χ σ hσ)
  let F : ℕ → ℂ := fun n =>
    ((mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 : ℂ)) *
      (companion φ (n / N) : ℂ)
  have hs' : HasSum F
      (verticalMellin σ (fun s => ∑' i, b i * mellinWeight φ s * (u i : ℂ) ^ (-s))) := by
    have hs1 : HasSum (fun n => F (n + 1))
        (verticalMellin σ (fun s => ∑' i, b i * mellinWeight φ s * (u i : ℂ) ^ (-s))) := by
      simpa only [F, b, u, Nat.cast_add, Nat.cast_one] using hs
    have := (hasSum_nat_add_iff 1).1 hs1
    simpa [F, mangoldt] using this
  calc
    characterPolynomial χ φ = ∑' n, F n :=
      (character_mellin_companion_tsum N hN χ φ hφ).symm
    _ = verticalMellin σ (fun s => ∑' i, b i * mellinWeight φ s * (u i : ℂ) ^ (-s)) := hs'.tsum_eq
    _ = -verticalMellin σ (fun s =>
        (N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s) := by
      unfold verticalMellin
      rw [← mul_neg, ← integral_neg]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      have hst : 1 / 2 < (line σ t).re := by simpa [line] using hσ
      rw [logDerivative_eq_neg_tsum χ hst, mul_neg, neg_neg,
        (summable_logDerivative_terms χ hst).tsum_eq_zero_add]
      simp only [mangoldt, ArithmeticFunction.map_zero,
        Complex.ofReal_zero, zero_mul, zero_div, zero_add]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp [u, b]
      calc
        _ = mellinWeight φ (line σ t) *
            (((mangoldt (n + 1) : ℂ) * χ (n + 1) /
              (n + 1 : ℕ) ^ (1 / 2 : ℂ)) *
              (((n + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-line σ t)) := by ring
        _ = _ := by
          rw [mellin_dirichlet_rescale (n + 1) N (by omega) hN]
          push_cast
          ring

end ConditionalGoldbach
