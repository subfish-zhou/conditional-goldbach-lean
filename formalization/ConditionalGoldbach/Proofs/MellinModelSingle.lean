module

public import ConditionalGoldbach.Proofs.MellinModelShift
public import ConditionalGoldbach.Proofs.ZetaGrowth

/-! Exact evaluation of the single model Mellin integral on every positive line. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

/-- Choose a comparison line to the right of `1` using the density growth bound
on the strip from the original contour to that line. -/
lemma exists_mellin_comparison_line (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ b D : ℝ, a ≤ b ∧ 1 < b ∧ 0 ≤ D ∧
      ∀ w : ℂ, w.re ∈ Icc a b → 1 ≤ |w.im| →
        ‖continuedDensity N w‖ ≤ D * (1 + |w.im|) := by
  obtain ⟨D, hD, hgrowth⟩ :=
    continuedDensity_vertical_growth N ha (show a < a + 2 by linarith)
  exact ⟨a + 2, D, by linarith, by linarith, hD, hgrowth⟩

lemma model_single_mellin (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => continuedDensity N (line a t) *
      mellin (fun y => (signedConvolution φ y : ℂ)) (line a t)) ∧
    verticalMellin a (fun w => continuedDensity N w *
      mellin (fun y => (signedConvolution φ y : ℂ)) w) =
      -(weightMass φ * singularSeries N : ℝ) := by
  obtain ⟨b, D, hab, hb, hD, hgrowth⟩ := exists_mellin_comparison_line N a ha
  exact model_single_mellin_shift_of_growth N hN hpos φ hφ a b ha hab hb D hD hgrowth

end ConditionalGoldbach
