import LiLiuGoldbach.Proofs.MellinModelShift
import LiLiuGoldbach.Proofs.ZetaGrowth

/-! Exact evaluation of the single model Mellin integral on every positive line. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma model_single_mellin (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => continuedDensity N (line a t) *
      mellin (fun y => (signedConvolution φ y : ℂ)) (line a t)) ∧
    verticalMellin a (fun w => continuedDensity N w *
      mellin (fun y => (signedConvolution φ y : ℂ)) w) =
      -(weightMass φ * singularSeries N : ℝ) := by
  obtain ⟨D, hD, hgrowth⟩ := continuedDensity_vertical_growth N ha (show a < a+2 by linarith)
  exact model_single_mellin_shift_of_growth N hN hpos φ hφ a (a+2) ha
    (by linarith) (by linarith) D hD hgrowth

end LiLiuGoldbach16
