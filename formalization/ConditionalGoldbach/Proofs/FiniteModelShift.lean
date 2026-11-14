module

public import ConditionalGoldbach.Proofs.FiniteModelRemovable
public import ConditionalGoldbach.Proofs.MellinModelShift

public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach.FiniteModel

lemma regularizedModelMellin_uniform_decay (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (D : ℝ) (hD : 0 ≤ D)
    (hgrowth : ∀ w : ℂ, w.re ∈ Icc a b → 1 ≤ |w.im| →
      ‖continuedDensity N w‖ ≤ D * (1 + |w.im|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖regularizedModelMellin N φ (line x t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2 := by
  obtain ⟨B, hB, hdec⟩ := signedConvolution_mellin_decay φ hφ a b ha hab
  exact regularized_mellin_product_decay (regularizedModelMellin N φ) (continuedDensity N)
    (mellin fun y => (signedConvolution φ y : ℂ)) a b
    (fun w hw => regularizedModelMellin_differentiableAt N φ hφ (ha.trans_le hw.1))
    (fun w hw => regularizedModelMellin_eq N φ hφ hw) D B hD hB.le hgrowth hdec

lemma model_single_mellin_shift_of_growth (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : 1 < b) (D : ℝ) (hD : 0 ≤ D)
    (hgrowth : ∀ w : ℂ, w.re ∈ Icc a b → 1 ≤ |w.im| →
      ‖continuedDensity N w‖ ≤ D * (1 + |w.im|)) :
    Integrable (fun t : ℝ => continuedDensity N (line a t) *
      mellin (fun y => (signedConvolution φ y : ℂ)) (line a t)) ∧
    verticalMellin a (fun w => continuedDensity N w *
      mellin (fun y => (signedConvolution φ y : ℂ)) w) =
      -(modelMass φ * singularSeries N : ℝ) := by
  obtain ⟨C, _, hbound⟩ := regularizedModelMellin_uniform_decay N φ hφ a b ha hab D hD hgrowth
  obtain ⟨hint, hshift⟩ := verticalMellin_shift_of_ae_eq (regularizedModelMellin N φ)
    (fun w => continuedDensity N w * mellin (fun y => (signedConvolution φ y : ℂ)) w)
    a b C hab
    (fun w hw => regularizedModelMellin_differentiableAt N φ hφ (ha.trans_le hw.1))
    hbound (regularizedModelMellin_line_ae N φ hφ a)
  exact ⟨hint, hshift.trans (regularizedModelMellin_initial N hN hpos φ hφ b hb).2⟩

end ConditionalGoldbach.FiniteModel
