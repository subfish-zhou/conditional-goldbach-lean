import ConditionalGoldbach.Proofs.WideFunctional
import ConditionalGoldbach.Proofs.FiniteQuadratic
import ConditionalGoldbach.Proofs.HardyArithmeticTheorems

/-! Exact recovery of the Appendix B wide-weight residual from the actual Hardy operator. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma wide_quadratic_residual_integral (hGRH : GRH experimentN) (ha : alpha experimentN < beta) :
    paperInner (residualOperator ha experimentN wideRieszVector) wideRieszVector =
      verticalMellin sigmaStar (fun s => verticalMellin sigmaStar (fun z =>
        (experimentN : ℂ)^(s+z)*mellin (fun u => (wideCompanion u : ℂ)) s*
          mellin (fun u => (wideCompanion u : ℂ)) z*residual experimentN s z)) := by
  apply finite_quadratic_residual_integral experimentN wideCompanion sigmaStar wide_sigmaStar_mem
    (by norm_num [sigmaStar]) wideRieszVector wideRieszVector_spec (residualOperator ha experimentN)
  exact proposition_5_4_kernel_pairing experimentN (by norm_num [experimentN]) experimentN_large hGRH ha

lemma proposition_B_4_of_scalar_identity (hGRH : GRH experimentN) (ha : alpha experimentN < beta)
    (hscalar : verticalMellin sigmaStar (fun s => verticalMellin sigmaStar (fun z =>
        (experimentN : ℂ)^(s+z)*mellin (fun u => (wideCompanion u : ℂ)) s*
          mellin (fun u => (wideCompanion u : ℂ)) z*residual experimentN s z)) = (wideResidual : ℂ)) :
    (∀ h : HardySpace (alpha experimentN) beta,
      Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line sigmaStar t) *
        mellin (fun u => (wideCompanion u : ℂ)) (line sigmaStar t) *
        (1 + line sigmaStar t) * fourierLaplace h (line sigmaStar t)) ∧
      wideFunctional h = paperInner h wideRieszVector) ∧
    (∃ ℓ : HardySpace (alpha experimentN) beta →L[ℂ] ℂ, ∀ h, ℓ h = wideFunctional h) ∧
    (wideResidual : ℂ) = paperInner (residualOperator ha experimentN wideRieszVector) wideRieszVector := by
  refine ⟨fun h => ⟨wideFunctional_integrable h,wideRieszVector_spec h⟩,
    wideFunctional_continuousLinearMap, ?_⟩
  rw [wide_quadratic_residual_integral hGRH ha,hscalar]

end ConditionalGoldbach
