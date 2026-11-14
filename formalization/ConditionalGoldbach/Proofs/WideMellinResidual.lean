module

public import ConditionalGoldbach.Proofs.WideMellinArithmetic
public import ConditionalGoldbach.Proofs.WideMellinModel
public import ConditionalGoldbach.Proofs.WideQuadratic

/-! The exact wide-weight residual and the full Appendix B.4 conclusion. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma wide_residual_mellin (hGRH : GRH experimentN) (σ : ℝ)
    (hσ : 0<σ) (hσupper : σ≤1/9) :
    Integrable (fun p : ℝ×ℝ => (experimentN:ℂ)^(line σ p.1+line σ p.2)*
      mellin (fun u => (wideCompanion u:ℂ)) (line σ p.1)*
      mellin (fun u => (wideCompanion u:ℂ)) (line σ p.2)*residual experimentN (line σ p.1) (line σ p.2)) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z => (experimentN:ℂ)^(s+z)*
      mellin (fun u => (wideCompanion u:ℂ)) s*mellin (fun u => (wideCompanion u:ℂ)) z*
      residual experimentN s z))=(wideResidual:ℂ) := by
  let M : ℂ→ℂ := mellin (fun u => (wideCompanion u:ℂ))
  let P : ℂ→ℂ→ℂ := fun s z => (experimentN:ℂ)^(s+z)*M s*M z*characterKernel experimentN s z
  let D : ℂ→ℂ→ℂ := fun s z => (experimentN:ℂ)^(s+z)*M s*M z*diagonalSeries experimentN (s+z)
  let K : ℂ→ℂ→ℂ := fun s z => (experimentN:ℂ)^(s+z)*M s*M z*continuedModel experimentN s z
  have hc (x y : ℝ) := weighted_continuedModel_cancel experimentN (by norm_num [experimentN]) wideWeight
    (line σ x) (line σ y) (mellin_betaDomain_line σ hσ hσupper x y)
  simp only [mellinWeight_wideWeight] at hc
  obtain ⟨hPi,hPv⟩ := wide_character_mellin hGRH σ hσ (by linarith)
  obtain ⟨hDi,hDv⟩ := wide_diagonal_mellin σ hσ
  obtain ⟨hKi',hKv'⟩ := wide_model_mellin σ hσ hσupper
  have hKi : Integrable (fun p : ℝ×ℝ => K (line σ p.1) (line σ p.2)) :=
    hKi'.congr (Eventually.of_forall (fun p => (hc p.1 p.2).symm))
  have hKv : verticalMellin σ (fun s => verticalMellin σ (K s)) =
      -(wideModelMass*singularSeries experimentN:ℝ) := by
    rw [← hKv']
    unfold verticalMellin
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    exact hc x y
  have hsplit (s z : ℂ) : (experimentN:ℂ)^(s+z)*M s*M z*residual experimentN s z=
      (P s z-D s z)-K s z := by dsimp [P,D,K,residual]; ring
  constructor
  · change Integrable (fun p : ℝ×ℝ => (experimentN:ℂ)^(line σ p.1+line σ p.2)*M (line σ p.1)*M (line σ p.2)*residual experimentN (line σ p.1) (line σ p.2))
    simp_rw [hsplit]
    exact (hPi.sub hDi).sub hKi
  · change verticalMellin σ (fun s => verticalMellin σ (fun z => (experimentN:ℂ)^(s+z)*M s*M z*residual experimentN s z))=_
    simp_rw [hsplit]
    rw [double_verticalMellin_sub σ _ K (hPi.sub hDi) hKi,
      double_verticalMellin_sub σ P D hPi hDi,hPv,hDv,hKv]
    unfold wideResidual
    push_cast
    ring

theorem proposition_B_4 (hGRH : GRH experimentN) (ha : alpha experimentN < beta) :
    (∀ h : HardySpace (alpha experimentN) beta,
      Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line sigmaStar t) *
        mellin (fun u => (wideCompanion u : ℂ)) (line sigmaStar t) *
        (1 + line sigmaStar t) * fourierLaplace h (line sigmaStar t)) ∧
      wideFunctional h = paperInner h wideRieszVector) ∧
    (∃ ℓ : HardySpace (alpha experimentN) beta →L[ℂ] ℂ, ∀ h, ℓ h = wideFunctional h) ∧
    (wideResidual : ℂ) = paperInner (residualOperator ha experimentN wideRieszVector) wideRieszVector := by
  exact proposition_B_4_of_scalar_identity hGRH ha
    (wide_residual_mellin hGRH sigmaStar (by norm_num [sigmaStar]) (by norm_num [sigmaStar])).2

end ConditionalGoldbach
