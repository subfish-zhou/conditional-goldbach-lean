module

public import ConditionalGoldbach.Proofs.FiniteModelShift
public import ConditionalGoldbach.Proofs.MellinModelSingle

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach.FiniteModel

lemma model_single_mellin (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => continuedDensity N (line a t) *
      mellin (fun y => (signedConvolution φ y : ℂ)) (line a t)) ∧
    verticalMellin a (fun w => continuedDensity N w *
      mellin (fun y => (signedConvolution φ y : ℂ)) w) =
      -(modelMass φ * singularSeries N : ℝ) := by
  obtain ⟨b, D, hab, hb, hD, hgrowth⟩ := exists_mellin_comparison_line N a ha
  exact model_single_mellin_shift_of_growth N hN hpos φ hφ a b ha hab hb D hD hgrowth

end ConditionalGoldbach.FiniteModel
