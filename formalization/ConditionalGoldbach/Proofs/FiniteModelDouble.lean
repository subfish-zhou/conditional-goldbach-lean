import ConditionalGoldbach.Proofs.FiniteModelBetaRelation
import ConditionalGoldbach.Proofs.FiniteModelBound
import ConditionalGoldbach.Proofs.FiniteModelSingle
import ConditionalGoldbach.Proofs.MellinModelDouble

/-! The double model inversion for general C6 weights, without a symmetry assumption. -/
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
  rw [double_verticalMellin_diagonal _ σ (model_double_integrable N φ hφ σ hσ hσupper)]
  rw [← (model_single_mellin N hN hpos φ hφ (2*σ) (by linarith)).2]
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let w := line (2*σ) t
  have hw : w.re = 2*σ := by simp [w,line]
  have hbeta := (signedConvolution_mellin_beta φ hφ σ hσ hσupper w hw).2
  have he (s : ℂ) : mellinWeight φ s * mellinWeight φ (w-s) *
      continuedDensity N (s+(w-s)) * betaKernel s (w-s) =
      continuedDensity N w * (mellinWeight φ s * mellinWeight φ (w-s) * betaKernel s (w-s)) := by
    rw [add_sub_cancel]
    ring
  change (2*(Real.pi : ℂ))⁻¹ *
    (∫ u : ℝ, mellinWeight φ (line σ u) * mellinWeight φ (w-line σ u) *
      continuedDensity N (line σ u+(w-line σ u)) * betaKernel (line σ u) (w-line σ u)) = _
  simp_rw [he]
  rw [integral_const_mul]
  change (2*(Real.pi : ℂ))⁻¹ * (continuedDensity N w * _) =
    continuedDensity N w * mellin (fun y => (signedConvolution φ y : ℂ)) w
  rw [hbeta]
  unfold verticalMellin
  ring

end ConditionalGoldbach.FiniteModel
