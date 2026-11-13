import LiLiuGoldbach.Proofs.FiniteModelRemovable
import LiLiuGoldbach.Proofs.MellinModelShift

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16.FiniteModel

lemma regularizedModelMellin_uniform_decay (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (D : ℝ) (hD : 0 ≤ D)
    (hgrowth : ∀ w : ℂ, w.re ∈ Icc a b → 1 ≤ |w.im| →
      ‖continuedDensity N w‖ ≤ D * (1 + |w.im|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖regularizedModelMellin N φ (line x t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2 := by
  obtain ⟨B, hB, hdec⟩ := signedConvolution_mellin_decay φ hφ a b ha hab
  apply uniform_vertical_decay_of_far_bound (regularizedModelMellin N φ) a b
    (fun w hw => regularizedModelMellin_differentiableAt N φ hφ (ha.trans_le hw.1))
    (D * B) (mul_nonneg hD hB.le)
  intro x hx t ht
  have hre : (line x t).re ∈ Icc a b := by simpa [line] using hx
  have him : (line x t).im = t := by simp [line]
  have hn : line x t ≠ 1 := by
    intro he
    have hz := congrArg Complex.im he
    rw [him, one_im] at hz
    simp [hz] at ht
    linarith
  rw [regularizedModelMellin_eq N φ hφ hn, norm_mul]
  have hprod := mul_le_mul (hgrowth _ hre (by simpa only [him] using ht))
    (hdec x hx t) (norm_nonneg _) (by positivity)
  rw [him] at hprod
  apply hprod.trans
  have hp : 0 < 1 + |t| := by positivity
  have hi : 0 ≤ (1 + |t|)⁻¹ := inv_nonneg.mpr hp.le
  have hi1 : (1 + |t|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg t])
  have hpow : (1 + |t|)⁻¹ ^ 5 ≤ (1 + |t|)⁻¹ ^ 2 :=
    pow_le_pow_of_le_one hi hi1 (by norm_num)
  have he : (D * (1 + |t|)) * (B * (1 + |t|)⁻¹ ^ 6) =
      (D * B) * (1 + |t|)⁻¹ ^ 5 := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hD hB.le)

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
  obtain ⟨C, hC, hbound⟩ := regularizedModelMellin_uniform_decay N φ hφ a b ha hab D hD hgrowth
  have hint (x : ℝ) (hx : x ∈ Icc a b) :
      Integrable (fun t : ℝ => regularizedModelMellin N φ (line x t)) := by
    apply integrable_of_uniform_vertical_decay _ x C
    · apply continuous_iff_continuousAt.mpr
      intro t
      exact (regularizedModelMellin_differentiableAt N φ hφ
        (by simpa [line] using ha.trans_le hx.1)).continuousAt.comp (by unfold line; fun_prop)
    · exact hbound x hx
  constructor
  · exact (hint a ⟨le_rfl, hab⟩).congr (regularizedModelMellin_line_ae N φ hφ a)
  · rw [← regularizedModelMellin_verticalMellin N φ hφ a,
      verticalMellin_eq_of_uniform_decay (regularizedModelMellin N φ) a b C hab
        (fun w hw => regularizedModelMellin_differentiableAt N φ hφ (ha.trans_le hw.1))
        (hint a ⟨le_rfl, hab⟩) (hint b ⟨hab, le_rfl⟩) hbound,
      (regularizedModelMellin_initial N hN hpos φ hφ b hb).2]

end LiLiuGoldbach16.FiniteModel
