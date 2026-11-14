module

public import ConditionalGoldbach.Proofs.CharacterReferencePolynomial

/-! The reference-line energy estimate from a pointwise smoothed-polynomial estimate. -/
public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma logarithmic_height_square_integrable :
    Integrable (fun t : ℝ => Real.log (|t| + 2) ^ 2 / (1 + t ^ 2)) := by
  let A : ℝ := 4 * (2 : ℝ) ^ (1 / 4 : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : Continuous (fun t : ℝ => Real.log (|t| + 2) ^ 2 / (1 + t ^ 2)) := by
    apply Continuous.div
    · exact ((continuous_abs.add continuous_const).log (by intro t; change |t| + 2 ≠ 0; positivity)).pow 2
    · fun_prop
    · intro t; positivity
  apply (hardy_decay_integrable.const_mul (4 * A ^ 2)).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hv : ‖(Real.log (|t| + 2) : ℂ)‖ ≤ A * (1 + |t|) ^ (1 / 4 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by nlinarith [abs_nonneg t]))]
    calc
      _ ≤ (|t| + 2) ^ (1 / 4 : ℝ) / (1 / 4) :=
        Real.log_le_rpow_div (by positivity) (by norm_num)
      _ ≤ (2 * (1 + |t|)) ^ (1 / 4 : ℝ) / (1 / 4) := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t]) (by norm_num)
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; dsimp [A]; ring
  have hb := weighted_line_square_bound (by norm_num : (0 : ℝ) ≤ 0) t A hA _ hv
  simpa only [norm_div, div_pow, norm_one_add_line_sq, add_zero, one_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb

lemma conductor_logarithm_energy_bound : ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, Real.exp 1 ≤ n →
    Integrable (fun t : ℝ => Real.log (n * (|t| + 2)) ^ 2 / (1 + t ^ 2)) ∧
    (∫ t : ℝ, Real.log (n * (|t| + 2)) ^ 2 / (1 + t ^ 2)) ≤ C * Real.log n ^ 2 := by
  let H : ℝ := ∫ t : ℝ, Real.log (|t| + 2) ^ 2 / (1 + t ^ 2)
  have hH : 0 ≤ H := integral_nonneg (by intro t; positivity)
  refine ⟨2 * Real.pi + 2 * H, by positivity, ?_⟩
  intro n hn
  have hn0 : 0 < n := (Real.exp_pos 1).trans_le hn
  have hl : 1 ≤ Real.log n := by simpa using Real.log_le_log (Real.exp_pos 1) hn
  have hb (t : ℝ) : Real.log (n * (|t| + 2)) ^ 2 / (1 + t ^ 2) ≤
      2 * Real.log n ^ 2 * (1 + t ^ 2)⁻¹ +
        2 * (Real.log (|t| + 2) ^ 2 / (1 + t ^ 2)) := by
    rw [Real.log_mul hn0.ne' (by positivity : |t| + 2 ≠ 0)]
    have hs : (Real.log n + Real.log (|t| + 2)) ^ 2 ≤
        2 * Real.log n ^ 2 + 2 * Real.log (|t| + 2) ^ 2 := by nlinarith [sq_nonneg (Real.log n - Real.log (|t| + 2))]
    convert div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 1 + t ^ 2) using 1; ring
  have hi : Integrable (fun t : ℝ => 2 * Real.log n ^ 2 * (1 + t ^ 2)⁻¹ +
      2 * (Real.log (|t| + 2) ^ 2 / (1 + t ^ 2))) :=
    (integrable_inv_one_add_sq.const_mul _).add (logarithmic_height_square_integrable.const_mul 2)
  have hf : Integrable (fun t : ℝ => Real.log (n * (|t| + 2)) ^ 2 / (1 + t ^ 2)) := by
    apply hi.mono' ?_ (Eventually.of_forall (fun t => ?_))
    · apply Continuous.aestronglyMeasurable
      apply Continuous.div
      · exact ((continuous_const.mul (continuous_abs.add continuous_const)).log
          (by intro t; change n * (|t| + 2) ≠ 0; positivity)).pow 2
      · fun_prop
      · intro t; positivity
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.log (n * (|t| + 2)) ^ 2 / (1 + t ^ 2))] using hb t
  refine ⟨hf, (integral_mono hf hi hb).trans ?_⟩
  rw [integral_add (integrable_inv_one_add_sq.const_mul _) (logarithmic_height_square_integrable.const_mul 2),
    integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq]
  change 2 * Real.log n ^ 2 * Real.pi + 2 * H ≤ (2 * Real.pi + 2 * H) * Real.log n ^ 2
  have hs : 1 ≤ Real.log n ^ 2 := by nlinarith
  nlinarith

lemma odd_character_average_mass (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) :
    (2 / (N.totient : ℝ)) * ((oddCharacters N).card : ℝ) = 1 := by
  have h := odd_character_short_parseval N hN hN4 {1} (fun _ => (1 : ℂ)) (by
    intro n hn _
    simp only [Finset.mem_singleton] at hn
    subst n
    omega)
  simpa [Finset.filter_singleton] using h

lemma smoothed_polynomial_continuous (N : ℕ) [NeZero N] (χ : Character N) (σ : ℝ) :
    Continuous (fun t : ℝ => smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)) := by
  unfold smoothedDirichletPolynomial
  apply continuous_finsetSum
  intro n hn
  by_cases h0 : n = 0
  · subst n
    simp [mangoldt]
    exact continuous_const
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast h0
    simp only [Complex.cpow_def_of_ne_zero hn0]
    unfold line
    fun_prop

lemma smoothed_polynomial_weighted_integrable (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun t : ℝ =>
      ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 / (1 + t ^ 2)) := by
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  let D := (1 + σ) * (Real.log 4 + 4) / σ ^ 2
  have hb (t : ℝ) :
      ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 ≤
        D * ((N.totient : ℝ) / 2) := by
    have h := smoothed_polynomial_average_bound N hN hN4 σ t hσ
    have hs := Finset.single_le_sum (fun ψ (_ : ψ ∈ oddCharacters N) =>
      sq_nonneg ‖smoothedDirichletPolynomial ψ ((N : ℝ) / 2) (1 / 2 + line σ t)‖) hχ
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 / (N.totient : ℝ) by positivity)
    have hf : 2 / (N.totient : ℝ) *
        ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 ≤ D := hm.trans h
    have hh : ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 ≤ D / (2 / (N.totient : ℝ)) :=
      (le_div_iff₀ (by positivity : 0 < 2 / (N.totient : ℝ))).mpr (by simpa only [mul_comm] using hf)
    convert hh using 1; simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  refine (integrable_inv_one_add_sq.const_mul (D * ((N.totient : ℝ) / 2))).mono' ?_ ?_
  · exact (((smoothed_polynomial_continuous N χ σ).norm.pow 2).div (by fun_prop)
      (by intro t; positivity)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right (hb t) (by positivity : 0 ≤ 1 + t ^ 2)

lemma smoothed_polynomial_average_energy (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (σ : ℝ) (hσ : 0 < σ) :
    (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
      (∫ t : ℝ, ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 / (1 + t ^ 2)) ≤
        Real.pi * ((1 + σ) * (Real.log 4 + 4) / σ ^ 2) := by
  let f (χ : Character N) (t : ℝ) :=
    ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 / (1 + t ^ 2)
  have hi (χ : Character N) (hχ : χ ∈ oddCharacters N) : Integrable (f χ) :=
    smoothed_polynomial_weighted_integrable N hN hN4 χ hχ σ hσ
  rw [← MeasureTheory.integral_finsetSum _ hi, ← integral_const_mul]
  have hright := integrable_inv_one_add_sq.const_mul ((1 + σ) * (Real.log 4 + 4) / σ ^ 2)
  have hb (t : ℝ) : (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N, f χ t ≤
      ((1 + σ) * (Real.log 4 + 4) / σ ^ 2) * (1 + t ^ 2)⁻¹ := by
    dsimp [f]
    rw [← Finset.sum_div, ← mul_div_assoc]
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right
      (smoothed_polynomial_average_bound N hN hN4 σ t hσ) (by positivity : 0 ≤ 1 + t ^ 2)
  have h := integral_mono ((MeasureTheory.integrable_finsetSum _ hi).const_mul (2 / (N.totient : ℝ))) hright hb
  simp only [integral_const_mul, integral_univ_inv_one_add_sq] at h
  simpa only [integral_const_mul, mul_comm] using h

lemma averagedLogDerivative_bound_of_polynomial (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (σ A L : ℝ) (hσ : 0 < σ) (_hA : 0 ≤ A)
    (hlogi : Integrable (fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) ^ 2 / (1 + t ^ 2)))
    (hloge : (∫ t : ℝ, Real.log ((N : ℝ) * (|t| + 2)) ^ 2 / (1 + t ^ 2)) ≤ L)
    (hpoint : ∀ χ ∈ oddCharacters N, ∀ t : ℝ,
      ‖logDerivative χ (line σ t)‖ ≤ A *
        (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ +
          Real.log ((N : ℝ) * (|t| + 2)))) :
    averagedLogDerivative N σ ≤
      2 * A ^ 2 * (Real.pi * ((1 + σ) * (Real.log 4 + 4) / σ ^ 2) + L) := by
  let P (χ : Character N) := ∫ t : ℝ,
    ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 / (1 + t ^ 2)
  have he (χ : Character N) (hχ : χ ∈ oddCharacters N) :
      (∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2)) ≤ 2 * A ^ 2 * (P χ + L) := by
    have hpi := smoothed_polynomial_weighted_integrable N hN hN4 χ hχ σ hσ
    have hgi := logDerivative_weighted_square_integrable N hN4 hGRH χ hχ σ hσ
    have hb (t : ℝ) : ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2) ≤
        2 * A ^ 2 * (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 / (1 + t ^ 2) +
          Real.log ((N : ℝ) * (|t| + 2)) ^ 2 / (1 + t ^ 2)) := by
      have hs := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hpoint χ hχ t))).mpr (hpoint χ hχ t)
      have hv : ‖logDerivative χ (line σ t)‖ ^ 2 ≤ 2 * A ^ 2 *
          (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ ^ 2 +
            Real.log ((N : ℝ) * (|t| + 2)) ^ 2) := by
        have hm := mul_nonneg (sq_nonneg A) (sq_nonneg
          (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line σ t)‖ -
            Real.log ((N : ℝ) * (|t| + 2))))
        nlinarith
      convert div_le_div_of_nonneg_right hv (by positivity : 0 ≤ 1 + t ^ 2) using 1; ring
    have hi := integral_mono hgi ((hpi.add hlogi).const_mul (2 * A ^ 2)) hb
    rw [integral_const_mul] at hi
    simp only [Pi.add_apply] at hi
    rw [integral_add hpi hlogi] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hloge) (by positivity))
  unfold averagedLogDerivative
  calc
    _ ≤ (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N, 2 * A ^ 2 * (P χ + L) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum he) (by positivity)
    _ = 2 * A ^ 2 * ((2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N, P χ + L) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const]
      simp only [nsmul_eq_mul]
      have hm := odd_character_average_mass N hN hN4
      calc
        _ = 2 * A ^ 2 * ((2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N, P χ +
          ((2 / (N.totient : ℝ)) * (oddCharacters N).card) * L) := by ring
        _ = _ := by rw [hm, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (smoothed_polynomial_average_energy N hN hN4 σ hσ) le_rfl) (by positivity)

lemma reference_line_energy_of_pointwise (A : ℝ) (hA : 0 < A)
    (hpoint : ∀ N : ℕ, ∀ (_ : NeZero N), Even N → Real.exp 10 < (N : ℝ) → GRH N →
      ∀ χ ∈ oddCharacters N, ∀ t : ℝ,
      ‖logDerivative χ (line (2 / Real.log N) t)‖ ≤ A *
        (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line (2 / Real.log N) t)‖ +
          Real.log ((N : ℝ) * (|t| + 2)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
      Real.exp 10 < (N : ℝ) → GRH N →
        averagedLogDerivative N (2 / Real.log N) ≤ C * Real.log N ^ 2 := by
  obtain ⟨L, hL, hlog⟩ := conductor_logarithm_energy_bound
  refine ⟨2 * A ^ 2 * (Real.pi * (Real.log 4 + 4) + L), by positivity, ?_⟩
  intro N _ hN hlarge hGRH
  have hN4 := (large_parameters hlarge).1
  have hln : 10 < Real.log N := by
    have hn : 0 < (N : ℝ) := (Real.exp_pos 10).trans hlarge
    exact (Real.lt_log_iff_exp_lt hn).mpr hlarge
  have hσ : 0 < 2 / Real.log N := by positivity
  have hnexp : Real.exp 1 ≤ (N : ℝ) := (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 10)).trans hlarge.le
  obtain ⟨hli, hle⟩ := hlog N hnexp
  apply (averagedLogDerivative_bound_of_polynomial N hN hN4 hGRH _ A (L * Real.log N ^ 2) hσ hA.le
    hli hle (hpoint N inferInstance hN hlarge hGRH)).trans
  have hD : (1 + 2 / Real.log N) * (Real.log 4 + 4) / (2 / Real.log N) ^ 2 ≤
      (Real.log 4 + 4) * Real.log N ^ 2 := by
    have hσ1 : 2 / Real.log N ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hlog4 : 0 < Real.log 4 + 4 := by positivity
    have he : (2 / Real.log N) ^ 2 * Real.log N ^ 2 = 4 := by field_simp; ring
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    calc
      _ ≤ 2 * (Real.log 4 + 4) := mul_le_mul_of_nonneg_right (by linarith) hlog4.le
      _ ≤ 4 * (Real.log 4 + 4) := by nlinarith
      _ = _ := by rw [mul_assoc, mul_comm (Real.log N ^ 2), he]; ring
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hD Real.pi_pos.le) (le_refl (L * Real.log N ^ 2))) (show 0 ≤ 2 * A ^ 2 by positivity)
  convert hh using 1; ring

end ConditionalGoldbach
