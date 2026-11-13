import LiLiuGoldbach

/-! Independently stated semantic bridges for TeX sections 1--4.
These invoke proved results only after their exact conclusions have been checked.
No theorem of the paper is promoted to an axiom or a hypothesis here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex LiLiuGoldbach16
namespace TexAudit14
attribute [local instance] Classical.propDecidable conductorNeZero

theorem weight_has_required_compact_support (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    HasCompactSupport φ ∧ 0 < weightMass φ :=
  ⟨hφ.hasCompactSupport, weightMass_pos hφ⟩

theorem universal_product_formula : C2 =
    ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  unfold C2 MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct
  congr 1
  funext p
  unfold MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation
  split_ifs <;> ring

theorem singular_series_formula (N : ℕ) : singularSeries N =
    2 * C2 * ∏ p ∈ N.primeFactors.filter (fun p => 2 < p),
      ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  unfold singularSeries C2 MathlibNt.SieveTheory.SingularSeries.liuSingularSeries
    MathlibNt.SieveTheory.SingularSeries.liuCorrection
    MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor
  ring

-- Replacing g_(bar chi)(z) by conj(g_chi(conj z)) is proved, not assumed.
theorem character_kernel_original_formula (N : ℕ) [NeZero N] (s z : ℂ) :
    characterKernel N s z = (2 / (N.totient : ℂ)) *
      ∑ χ ∈ oddCharacters N, logDerivative χ s * logDerivative (star χ) z :=
  characterKernel_eq_star_sum N s z

-- PositiveKernel alone contains only a real-part inequality. The missing
-- Hermitian condition is proved for this specific kernel and included here.
theorem character_kernel_full_positive (N : ℕ) [NeZero N] :
    HermitianKernel (fun s z => characterKernel N s (conj z)) ∧
    PositiveKernel (fun s z => characterKernel N s (conj z)) :=
  ⟨characterKernel_hermitian N, characterKernel_positive N⟩

-- finrank <= k alone would be insufficient for an infinite-dimensional span.
-- The independently named finite-dimensional theorem closes that loophole.
theorem character_kernel_rank_meaning (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) ∧
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun z : ℂ => fun s : ℂ => characterKernel N s (conj z)))) ≤ N.totient / 2 :=
  ⟨proposition_3_2_finite_rank N hN hN4, (proposition_3_2 N hN hN4).2.2.2.2.2.2⟩

-- TeX 1242--1243 specifies an entire continuation of the displayed formula.
-- A pointwise Gamma*L product at Gamma poles would not be an acceptable replacement.
theorem completed_function_meaning {d : ℕ} [NeZero d] (χ : Character d)
    (hodd : χ (-1) = -1) (hprim : χ.IsPrimitive) :
    Differentiable ℂ (completedL χ) ∧
    (∀ z : ℂ, 0 < z.re → completedL χ z =
      (d : ℂ)^((z+1)/2) * (Real.pi : ℂ)^(-(z+1)/2) *
        Gamma ((z+1)/2) * χ.LFunction z) ∧
    (∀ z : ℂ, completedL χ z = 0 ↔
      0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0) ∧
    (∀ z : ℂ, 0 < z.re →
      analyticOrderAt (completedL χ) z = analyticOrderAt χ.LFunction z) := by
  have hne : χ ≠ 1 := odd_character_ne_one χ hodd
  exact ⟨completedL_differentiable χ hne,
    fun _ hz => completedL_odd_formula χ hodd hz,
    fun z => completedL_eq_zero_iff χ hne hprim z,
    fun _ hz => completedL_order_eq_LFunction χ hne hz⟩

theorem beta_integral_continuation_bridge (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    betaIntegral u v = betaGamma u v :=
  betaIntegral_eq_Gamma_mul_div u v hu hv

theorem beta_bound_rhs_is_nonnegative (σ : ℝ) :
    0 ≤ (2 * betaIntegral (1 / 2 - σ) (2 * σ) +
      betaIntegral (1 / 2 - σ) (1 / 2 - σ)).re := by
  have h₁ := betaIntegral_real_nonneg (1 / 2 - σ) (2 * σ)
  have h₂ := betaIntegral_real_nonneg (1 / 2 - σ) (1 / 2 - σ)
  push_cast at h₁ h₂
  norm_num [Complex.mul_re]
  linarith

theorem beta_bound_rhs_norm_is_re (σ : ℝ) :
    ‖2 * betaIntegral (1 / 2 - σ) (2 * σ) +
      betaIntegral (1 / 2 - σ) (1 / 2 - σ)‖ =
      (2 * betaIntegral (1 / 2 - σ) (2 * σ) +
        betaIntegral (1 / 2 - σ) (1 / 2 - σ)).re := by
  let z := 2 * betaIntegral ((1 : ℂ) / 2 - σ) (2 * σ) +
      betaIntegral (1 / 2 - σ) (1 / 2 - σ)
  have hi : z.im = 0 := by
    have h₁ := betaIntegral_real (1 / 2 - σ) (2 * σ)
    have h₂ := betaIntegral_real (1 / 2 - σ) (1 / 2 - σ)
    push_cast at h₁ h₂
    dsimp [z]
    rw [h₁, h₂]
    simp
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  change ‖z‖ = z.re
  conv_lhs => rw [he]
  exact Complex.norm_of_nonneg (beta_bound_rhs_is_nonnegative σ)

theorem prime_count_members_have_both_support_bounds (N p : ℕ)
    (hp : p ∈ (Finset.range (N + 1)).filter (fun p =>
      p.Prime ∧ (N - p).Prime ∧ (N : ℝ) / 3 ≤ p ∧ (p : ℝ) ≤ 2 * N / 3)) :
    p.Prime ∧ (N - p).Prime ∧ p + (N - p) = N ∧
      (N : ℝ) / 3 ≤ p ∧ (p : ℝ) ≤ 2 * N / 3 ∧
      (N : ℝ) / 3 ≤ (N - p : ℕ) ∧ ((N - p : ℕ) : ℝ) ≤ 2 * N / 3 := by
  rcases Finset.mem_filter.mp hp with ⟨hrange, hprime, hother, hlo, hhi⟩
  have hpN : p ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
  refine ⟨hprime, hother, Nat.add_sub_of_le hpN, hlo, hhi, ?_, ?_⟩
  · rw [Nat.cast_sub hpN]
    linarith
  · rw [Nat.cast_sub hpN]
    linarith

#print axioms weight_has_required_compact_support
#print axioms universal_product_formula
#print axioms singular_series_formula
#print axioms character_kernel_original_formula
#print axioms character_kernel_full_positive
#print axioms character_kernel_rank_meaning
#print axioms completed_function_meaning
#print axioms beta_integral_continuation_bridge
#print axioms beta_bound_rhs_is_nonnegative
#print axioms beta_bound_rhs_norm_is_re
#print axioms prime_count_members_have_both_support_bounds
end TexAudit14
