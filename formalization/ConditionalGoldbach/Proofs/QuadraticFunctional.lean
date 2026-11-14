module

public import ConditionalGoldbach.Proofs.QuadraticNormChange
public import ConditionalGoldbach.Proofs.QuadraticAsymptotic

/-! Complete Proposition 7.4: functional existence, norm, and quantitative asymptotic. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

theorem proposition_7_4 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ N : ℕ, Even N → Real.exp 10 < (N : ℝ) →
      (∀ σ ∈ Ioo (alpha N) beta,
        (∀ h : HardySpace (alpha N) beta,
          Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) *
            (1 + line σ t) * fourierLaplace h (line σ t)) ∧
          functionalValue N φ σ h = paperInner h (rieszVector N φ)) ∧
        ∃ ℓ : HardySpace (alpha N) beta →L[ℂ] ℂ,
          (∀ h, ℓ h = functionalValue N φ σ h) ∧
          ‖ℓ‖ ^ 2 = normFunctional N φ (alpha N)) ∧
      ‖(rieszVector N φ : HardySpace (alpha N) beta)‖ ^ 2 = normFunctional N φ (alpha N) ∧
      normFunctional N φ (alpha N) ≤ Real.exp 2 * weightEnergy φ) ∧
    (∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      |normFunctional N φ (alpha N) - Real.exp 2 * weightEnergy φ| ≤ C / Real.log N))  := by
  refine ⟨?_, normFunctional_asymptotic φ hφ⟩
  intro N _ hlarge
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 10).trans hlarge
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hlog : 10 < Real.log N := by
    have h := Real.log_lt_log (Real.exp_pos 10) hlarge
    simpa using h
  have ha : sigmaStar ∈ Ioo (alpha N) beta := by
    constructor
    · unfold sigmaStar alpha
      apply (div_lt_div_iff₀ (by linarith : 0 < Real.log N) (by norm_num : (0 : ℝ) < 9)).2
      linarith
    · norm_num [sigmaStar, beta]
  obtain ⟨hv, hn⟩ := rieszVector_density_spec N hNnat φ hφ ha
  rw [← normFunctional_density_integral] at hn
  refine ⟨?_, hn, normFunctional_le_exp2_weightEnergy N hlarge φ hφ⟩
  · intro σ hσ
    constructor
    · intro ψ
      exact ⟨functionalValue_integrable N hNnat φ hφ σ hσ ψ, hv σ hσ ψ⟩
    · obtain ⟨ℓ, hℓ, hnorm⟩ := functionalValue_continuousLinearMap N hNnat φ hφ σ hσ
      refine ⟨ℓ, hℓ, ?_⟩
      rw [← normFunctional_density_integral] at hnorm
      exact hnorm
      exact hNnat
  · exact hNnat

end ConditionalGoldbach
