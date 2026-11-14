module

public import ConditionalGoldbach.Proofs.FiniteModelDouble
public import ConditionalGoldbach.Proofs.WideModelData

/-! The actual model term for the paper's finitely smooth wide companion. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma wide_model_mellin (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) :
    Integrable (fun p : ℝ × ℝ =>
      mellin (fun u => (wideCompanion u : ℂ)) (line σ p.1) *
      mellin (fun u => (wideCompanion u : ℂ)) (line σ p.2) *
      continuedDensity experimentN (line σ p.1+line σ p.2) * betaKernel (line σ p.1) (line σ p.2)) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellin (fun u => (wideCompanion u : ℂ)) s * mellin (fun u => (wideCompanion u : ℂ)) z *
      continuedDensity experimentN (s+z) * betaKernel s z)) =
        -(wideModelMass*singularSeries experimentN : ℝ) := by
  have hi := FiniteModel.model_double_integrable experimentN wideWeight wideFiniteModelWeight σ hσ hσupper
  have he := FiniteModel.model_double_mellin experimentN (by norm_num [experimentN,even_iff_two_dvd])
    (by norm_num [experimentN]) wideWeight wideFiniteModelWeight σ hσ hσupper
  simpa only [mellinWeight_wideWeight,finiteModel_mass_wideWeight] using And.intro hi he

end ConditionalGoldbach
