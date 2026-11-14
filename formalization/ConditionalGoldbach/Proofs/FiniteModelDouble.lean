module

public import ConditionalGoldbach.Proofs.FiniteModelBetaRelation
public import ConditionalGoldbach.Proofs.FiniteModelBound
public import ConditionalGoldbach.Proofs.FiniteModelSingle
public import ConditionalGoldbach.Proofs.MellinDoubleDiagonal

/-! The double model inversion for general C6 weights, without a symmetry assumption. -/
public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach.FiniteModel

lemma model_double_mellin (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s+z) * betaKernel s z)) =
        -(modelMass φ * singularSeries N : ℝ) := by
  rw [model_double_mellin_eq_single N φ σ
    (model_double_integrable N φ hφ σ hσ hσupper)
    (fun w hw => (signedConvolution_mellin_beta φ hφ σ hσ hσupper w hw).2)]
  exact (model_single_mellin N hN hpos φ hφ (2 * σ) (by linarith)).2

end ConditionalGoldbach.FiniteModel
