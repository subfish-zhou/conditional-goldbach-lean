import LiLiuGoldbach.Proofs.MellinCharacterShift

/-! Both audited contour regimes for the character moment, including absolute convergence. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

theorem lemma_3_5_absolute_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 1 / 2 < σ ∨ (GRH N ∧ 0 < σ ∧ σ ≤ 1 / 9)) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        characterKernel N (line σ p.1) (line σ p.2)) := by
  rcases hσ with hσ | ⟨hGRH,hσ,hσ'⟩
  · exact characterMoment_mellin_initial_integrable N φ hφ σ hσ
  · exact (characterMoment_mellin_shifted N hN hN4 hGRH φ hφ σ hσ (by linarith)).1

theorem lemma_3_5_small_sigma (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z)) := by
  exact (characterMoment_mellin_shifted N hN hN4 hGRH φ hφ σ hσ (by linarith)).2

end LiLiuGoldbach16
