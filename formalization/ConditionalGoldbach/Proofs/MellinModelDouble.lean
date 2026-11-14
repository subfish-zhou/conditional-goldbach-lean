module

public import ConditionalGoldbach.Proofs.MellinBetaRelation
public import ConditionalGoldbach.Proofs.MellinModelBound
public import ConditionalGoldbach.Proofs.MellinDiagonal
public import ConditionalGoldbach.Proofs.MellinDoubleDiagonal

/-! The complete original Lemma 7.2: diagonal and signed model inversion. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma model_double_mellin (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s+z) * betaKernel s z)) =
        -(weightMass φ * singularSeries N : ℝ) := by
  rw [model_double_mellin_eq_single N φ σ
    (model_double_integrable N φ hφ σ hσ hσupper)
    (fun w hw => (signedConvolution_mellin_beta φ hφ σ hσ hσupper w hw).2)]
  exact (model_single_mellin N hN hpos φ hφ (2 * σ) (by linarith)).2

theorem lemma_7_2 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * diagonalSeries N (s + z))) =
        diagonalMoment N φ ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s + z) * betaKernel s z)) =
        -(weightMass φ * singularSeries N : ℝ) := by
  exact ⟨(diagonalMoment_mellin N (by omega) φ hφ σ hσ).2,
    model_double_mellin N hN (by omega) φ hφ σ hσ hσ'⟩

theorem lemma_7_2_absolute_convergence (N : ℕ) [NeZero N]
    (_hN : Even N) (hN4 : 4 ≤ N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        diagonalSeries N (line σ p.1 + line σ p.2)) ∧
    Integrable (fun p : ℝ × ℝ =>
      mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        continuedDensity N (line σ p.1 + line σ p.2) *
        betaKernel (line σ p.1) (line σ p.2)) := by
  exact ⟨(diagonalMoment_mellin N (by omega) φ hφ σ hσ).1,
    model_double_integrable N φ hφ σ hσ hσ'⟩

end ConditionalGoldbach
