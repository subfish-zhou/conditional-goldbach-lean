module

public import ConditionalGoldbach.Proofs.CharacterGrowth
public import ConditionalGoldbach.Proofs.MellinContourShift
public import ConditionalGoldbach.Proofs.MellinDifferentiation
public import ConditionalGoldbach.Proofs.MellinMoment

/-! Character projection shifted to the GRH half-plane. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma log_square_polynomial_bound (N : ℕ) (hN : 4 ≤ N) (t : ℝ) :
    Real.log (N * (|t| + 2)) ^ 2 ≤ 4 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) * (|t| + 2) := by positivity
  have hone : 1 ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hl0 := Real.log_nonneg hone
  have hl := Real.log_le_sub_one_of_pos hpos
  have hbound : Real.log (N * (|t| + 2)) ≤ 2 * (N : ℝ) * (1 + |t|) := by
    nlinarith [abs_nonneg t]
  have hsq := sq_le_sq₀ hl0 (by positivity : 0 ≤ 2 * (N : ℝ) * (1 + |t|)) |>.mpr hbound
  nlinarith

lemma mellin_coefficient_differentiable (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ)
    (hφ : IsWeight φ) : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ s * mellinWeight φ s) := by
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  exact (differentiable_id.const_cpow (Or.inl hNz)).mul (mellinWeight_differentiable hφ)

lemma mellin_character_uniform_bound (N : ℕ) (hN : 4 ≤ N) (φ : ℝ → ℝ)
    (hφ : IsWeight φ) (lo A : ℝ) (hA : 0 ≤ A) (g : ℂ → ℂ)
    (hg : ∀ x ∈ Icc lo 1, ∀ t : ℝ,
      ‖g (line x t)‖ ≤ A * Real.log (N * (|t| + 2)) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc lo 1, ∀ t : ℝ,
      ‖(N : ℂ) ^ (line x t) * mellinWeight φ (line x t) * g (line x t)‖ ≤
        C * (1 + |t|)⁻¹ ^ 2 := by
  obtain ⟨B, hB, hb⟩ := mellin_test_rapid_decay (companion φ) (companion_contDiff hφ)
    (companion_support_subset hφ) lo 4
  refine ⟨(N : ℝ) * B * (4 * A * (N : ℝ) ^ 2), by positivity, ?_⟩
  intro x hx t
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNpow : ‖(N : ℂ) ^ (line x t)‖ ≤ N := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    have hline : (line x t).re = x := by simp [line]
    rw [hline]
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 hx.2
  have hm : ‖mellinWeight φ (line x t)‖ ≤ B * (1 + |t|)⁻¹ ^ 4 := by
    simpa only [mellinWeight, line, add_re, ofReal_re, mul_re, ofReal_im, I_re,
      I_im, mul_zero, zero_mul, sub_self, add_zero, add_im, mul_im, mul_one,
      zero_add] using hb (line x t) (by simpa [line] using hx.1)
  have hg' : ‖g (line x t)‖ ≤ (4 * A * (N : ℝ) ^ 2) * (1 + |t|) ^ 2 := by
    have h := (hg x hx t).trans (mul_le_mul_of_nonneg_left (log_square_polynomial_bound N hN t) hA)
    convert h using 1; ring
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ((N : ℝ) * (B * (1 + |t|)⁻¹ ^ 4)) *
        ((4 * A * (N : ℝ) ^ 2) * (1 + |t|) ^ 2) :=
      mul_le_mul (mul_le_mul hNpow hm (norm_nonneg _) hNpos.le) hg'
        (norm_nonneg _) (by positivity)
    _ = _ := by
      have ht : (1 + |t|) ≠ 0 := by positivity
      field_simp

lemma character_mellin_shift_of_log_bound {N : ℕ} [NeZero N] (hN : 4 ≤ N)
    (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hA : 0 ≤ A) (hg : ∀ x ∈ Icc σ 1, ∀ t : ℝ,
      ‖logDerivative χ (line x t)‖ ≤ A * Real.log (N * (|t| + 2)) ^ 2) :
    Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) *
      logDerivative χ (line σ t)) ∧
    characterPolynomial χ φ = -verticalMellin σ (fun s =>
      (N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s) := by
  let f : ℂ → ℂ := fun s => (N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s
  have hNpos : 0 < N := by omega
  have hd : ∀ z : ℂ, z.re ∈ Icc σ 1 → DifferentiableAt ℂ f z := by
    intro z hz
    exact ((mellin_coefficient_differentiable N hNpos φ hφ) z).mul
      (odd_logDerivative_analyticAt_of_GRH hGRH χ hχ (hσ.trans_le hz.1)).differentiableAt
  obtain ⟨C, _, hc⟩ := mellin_character_uniform_bound N hN φ hφ σ A hA (logDerivative χ) hg
  have hcont : Continuous (fun t : ℝ => f (line σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (hd (line σ t) (by simpa [line] using (show σ ∈ Icc σ 1 from ⟨le_rfl, hσ1⟩))).continuousAt.comp
    unfold line
    fun_prop
  have hi : Integrable (fun t : ℝ => f (line σ t)) :=
    integrable_of_uniform_vertical_decay f σ C hcont (hc σ ⟨le_rfl, hσ1⟩)
  refine ⟨hi, ?_⟩
  have hs := verticalMellin_eq_of_uniform_decay f σ 1 C hσ1 hd hi
    (character_mellin_initial_integrable χ φ hφ 1 (by norm_num)) hc
  rw [characterPolynomial_mellin_initial χ φ hφ 1 (by norm_num), ← hs]

lemma character_mellin_shift {N : ℕ} [NeZero N] (_hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) *
      logDerivative χ (line σ t)) ∧
    characterPolynomial χ φ = -verticalMellin σ (fun s =>
      (N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s) := by
  obtain ⟨A, hA, hg⟩ := logDerivative_uniform_bound σ 1 hσ hσ1
  exact character_mellin_shift_of_log_bound hN4 hGRH χ hχ φ hφ σ A hσ hσ1 hA.le
    (hg N inferInstance hN4 hGRH χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2))

theorem lemma_7_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ σ u : ℝ, 0 < u → (companion φ u : ℂ) =
      verticalMellin σ (fun s => mellinWeight φ s * (u : ℂ) ^ (-s))) ∧
    (∀ lo hi : ℝ, lo ≤ hi → ∃ C : ℝ, 0 < C ∧
      ∀ σ ∈ Icc lo hi, ∀ t : ℝ, ‖mellinWeight φ (line σ t)‖ ≤ C * (1 + |t|)⁻¹ ^ 6) ∧
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRH N →
      ∀ χ ∈ oddCharacters N, ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 →
        characterPolynomial χ φ = -verticalMellin σ (fun s =>
          (N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s)) := by
  refine ⟨mellinWeight_inversion hφ, mellinWeight_uniform_decay φ hφ, ?_⟩
  intro N _ hN hN4 hGRH χ hχ σ hσ hσ1
  exact (character_mellin_shift hN hN4 hGRH χ hχ φ hφ σ hσ (by linarith)).2

lemma characterMoment_mellin_shifted (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) * mellinWeight φ (line σ p.1) *
        mellinWeight φ (line σ p.2) * characterKernel N (line σ p.1) (line σ p.2)) ∧
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z)) := by
  have hi (χ : Character N) (hχ : χ ∈ oddCharacters N) :=
    character_mellin_shift hN hN4 hGRH χ hχ φ hφ σ hσ hσ1
  have hibar (χ : Character N) (hχ : χ ∈ oddCharacters N) :=
    character_mellin_shift hN hN4 hGRH (star χ) ((star_mem_oddCharacters χ).2 hχ) φ hφ σ hσ hσ1
  constructor
  · simp_rw [weighted_characterKernel_factor]
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro χ hχ
    exact (hi χ hχ).1.mul_prod (hibar χ hχ).1
  · simp_rw [weighted_characterKernel_factor]
    rw [double_verticalMellin_finset_prod (oddCharacters N) σ _ _ _
      (fun χ hχ => (hi χ hχ).1) (fun χ hχ => (hibar χ hχ).1)]
    unfold characterMoment
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro χ hχ
    calc
      _ = characterPolynomial χ φ * characterPolynomial (star χ) φ := by
        rw [characterPolynomial_star, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        rfl
      _ = _ := by rw [(hi χ hχ).2, (hibar χ hχ).2]; ring

theorem lemma_7_1_absolute_convergence (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ σ u : ℝ, 0 < u → Integrable (fun t : ℝ =>
      mellinWeight φ (line σ t) * (u : ℂ) ^ (-line σ t))) ∧
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → GRH N →
      ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 9 →
        (∀ χ ∈ oddCharacters N, Integrable (fun t : ℝ =>
          (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) * logDerivative χ (line σ t))) ∧
        Integrable (fun p : ℝ × ℝ =>
          (N : ℂ) ^ (line σ p.1 + line σ p.2) * mellinWeight φ (line σ p.1) *
            mellinWeight φ (line σ p.2) * characterKernel N (line σ p.1) (line σ p.2)) ∧
        (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
          (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z))) := by
  refine ⟨mellinWeight_inversion_integrable hφ, ?_⟩
  intro N _ hN hN4 hGRH σ hσ hσ1
  refine ⟨?_, characterMoment_mellin_shifted N hN hN4 hGRH φ hφ σ hσ (by linarith)⟩
  intro χ hχ
  exact (character_mellin_shift hN hN4 hGRH χ hχ φ hφ σ hσ (by linarith)).1

end ConditionalGoldbach
