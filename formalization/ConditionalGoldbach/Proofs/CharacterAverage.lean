module

public import ConditionalGoldbach.Proofs.SpectralPerronGamma
public import ConditionalGoldbach.Proofs.SpectralPerronTruncation
public import ConditionalGoldbach.Proofs.CharacterPoissonComparison
public import ConditionalGoldbach.Proofs.CharacterAverageAssembly

/-! The full uniform character average in Lemma 6.4. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma reference_line_pointwise_of_gamma_bound (CΓ : ℝ) (hCΓ : 0 < CΓ)
    (hGamma : ∀ X : ℝ, 2 ≤ X → ∀ u : ℂ, 1/2 ≤ u.re →
      Integrable (fun τ : ℝ => smoothedPerronKernel X (line 1 (2*Real.pi*τ)) *
        ((logDeriv Gamma ((u+line 1 (2*Real.pi*τ)+1)/2)-logDeriv Gamma ((u+1)/2))/2)) ∧
      ‖∫ τ : ℝ, smoothedPerronKernel X (line 1 (2*Real.pi*τ)) *
        ((logDeriv Gamma ((u+line 1 (2*Real.pi*τ)+1)/2)-logDeriv Gamma ((u+1)/2))/2)‖ ≤ CΓ) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
      Real.exp 10 < (N : ℝ) → GRH N → ∀ χ ∈ oddCharacters N, ∀ t : ℝ,
      ‖logDerivative χ (line (2 / Real.log N) t)‖ ≤ A *
        (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1/2+line (2 / Real.log N) t)‖ +
          Real.log ((N : ℝ)*(|t|+2))) := by
  obtain ⟨C₂,hC₂,hcompare⟩ := zeroPoisson_logDerivative_comparison
  refine ⟨3*(1+(CΓ+8)+C₂),by positivity,?_⟩
  intro N _ _ hlarge hGRH χ hχ t
  have hN4 := (large_parameters hlarge).1
  have hN4R : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hn : 0 < (N : ℝ) := by linarith
  have hln : 10 < Real.log N := (Real.lt_log_iff_exp_lt hn).mpr hlarge
  have hσ : 0 < referenceLine N := by unfold referenceLine; positivity
  have hσ1 : referenceLine N ≤ 1 := by
    unfold referenceLine
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hX2 : 2 ≤ (N : ℝ)/2 := by linarith
  have hΓ := hGamma ((N : ℝ)/2) hX2 (1/2+line (referenceLine N) t)
    (by simp [line]; exact hσ.le)
  have htr := smoothed_truncation_bound_of_gamma_integral hGRH χ hχ
    (by linarith : 1 < (N : ℝ)/2) hσ t CΓ hΓ.1 hΓ.2
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((N : ℝ)*(|t|+2)) :=
    Real.log_le_log hn (by nlinarith [abs_nonneg t])
  have hE : 1 ≤ Real.log ((N : ℝ)*(|t|+2)) := by linarith
  have htr' : ‖-logDerivative χ (line (referenceLine N) t) -
      smoothedDirichletPolynomial χ ((N : ℝ)/2) (1/2+line (referenceLine N) t)‖ ≤
      perronZeroCoefficient ((N : ℝ)/2) (referenceLine N) * zeroPoisson χ (referenceLine N) t +
        (CΓ+8)*Real.log ((N : ℝ)*(|t|+2)) := by
    apply htr.trans
    nlinarith [mul_nonneg hCΓ.le (sub_nonneg.mpr hE)]
  have hh := reference_logDerivative_bound_of_smoothed_truncation (CΓ+8) C₂
    (by positivity) hC₂.le N hlarge χ t htr'
    (hcompare N inferInstance hN4 hGRH χ hχ (referenceLine N) t hσ hσ1)
  simpa only [referenceLine] using hh

lemma lemma_6_4_of_gamma_bound (CΓ : ℝ) (hCΓ : 0 < CΓ)
    (hGamma : ∀ X : ℝ, 2 ≤ X → ∀ u : ℂ, 1/2 ≤ u.re →
      Integrable (fun τ : ℝ => smoothedPerronKernel X (line 1 (2*Real.pi*τ)) *
        ((logDeriv Gamma ((u+line 1 (2*Real.pi*τ)+1)/2)-logDeriv Gamma ((u+1)/2))/2)) ∧
      ‖∫ τ : ℝ, smoothedPerronKernel X (line 1 (2*Real.pi*τ)) *
        ((logDeriv Gamma ((u+line 1 (2*Real.pi*τ)+1)/2)-logDeriv Gamma ((u+1)/2))/2)‖ ≤ CΓ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
      Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ σ : ℝ, 0 < σ → σ ≤ beta →
        (∀ χ ∈ oddCharacters N,
          Integrable (fun t : ℝ => ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2))) ∧
        averagedLogDerivative N σ ≤ C * (Real.log N ^ 2 + σ⁻¹ ^ 2) := by
  obtain ⟨A,hA,hpoint⟩ := reference_line_pointwise_of_gamma_bound CΓ hCΓ hGamma
  apply lemma_6_4_of_reference_and_comparison (reference_line_energy_of_pointwise A hA hpoint)
  obtain ⟨C,hC,hcompare⟩ := zeroPoisson_logDerivative_comparison
  refine ⟨C,hC,?_⟩
  intro N _ _ hlarge hGRH χ hχ x hx hx1 t
  exact hcompare N inferInstance (large_parameters hlarge).1 hGRH χ hχ x t hx (by linarith)

lemma reference_line_pointwise : ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
    Real.exp 10 < (N : ℝ) → GRH N → ∀ χ ∈ oddCharacters N, ∀ t : ℝ,
    ‖logDerivative χ (line (2 / Real.log N) t)‖ ≤ A *
      (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1/2+line (2 / Real.log N) t)‖ +
        Real.log ((N : ℝ)*(|t|+2))) :=
  reference_line_pointwise_of_gamma_bound 16 (by norm_num)
    (fun _ hX _ hu => gamma_perron_integral_bound hX (by norm_num : (0:ℝ)<1) hu)

theorem lemma_6_4 : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ σ : ℝ, 0 < σ → σ ≤ beta →
      (∀ χ ∈ oddCharacters N,
        Integrable (fun t : ℝ => ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2))) ∧
      averagedLogDerivative N σ ≤ C * (Real.log N ^ 2 + σ⁻¹ ^ 2) :=
  lemma_6_4_of_gamma_bound 16 (by norm_num)
    (fun _ hX _ hu => gamma_perron_integral_bound hX (by norm_num : (0:ℝ)<1) hu)

end ConditionalGoldbach
