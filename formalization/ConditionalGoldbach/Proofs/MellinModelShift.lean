module

public import ConditionalGoldbach.Proofs.MellinModelRemovable

/-! Shifting the model's single Mellin contour across its removable point. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma uniform_vertical_decay_of_far_bound (f : ℂ → ℂ) (a b : ℝ)
    (hd : ∀ w : ℂ, w.re ∈ Icc a b → DifferentiableAt ℂ f w)
    (D : ℝ) (hD : 0 ≤ D)
    (hfar : ∀ x ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖f (line x t)‖ ≤ D * (1 + |t|)⁻¹ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2 := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ × ℝ => f (line p.1 p.2)) K := by
    intro p hp
    exact ((hd _ (by simpa [line] using hp.1)).continuousAt.comp
      (show ContinuousAt (fun p : ℝ × ℝ => line p.1 p.2) p by unfold line; fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨4 * (|B| + 1) + D, by positivity, fun x hx t => ?_⟩
  by_cases ht : 1 ≤ |t|
  · exact (hfar x hx t ht).trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg B]) (sq_nonneg _))
  · have ht' : |t| ≤ 1 := (lt_of_not_ge ht).le
    have hb : ‖f (line x t)‖ ≤ |B| + 1 :=
      (hB (x, t) ⟨hx, (abs_le.mp ht')⟩).trans (by linarith [le_abs_self B])
    have hi : (1 / 2 : ℝ) ≤ (1 + |t|)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 + |t|)
          (by linarith : 1 + |t| ≤ 2))
    have hi2 : (1 / 4 : ℝ) ≤ (1 + |t|)⁻¹ ^ 2 := by nlinarith
    have hnon : 0 ≤ |B| + 1 := by positivity
    nlinarith [mul_nonneg hD (sq_nonneg (1 + |t|)⁻¹), mul_le_mul_of_nonneg_left hi2 hnon]

/-- A regularized product inherits integrable vertical decay from linear growth of
one factor and sixth-power decay of the other. The factors agree with the
regularization away from the removable point at `1`. -/
lemma regularized_mellin_product_decay (regularized density transform : ℂ → ℂ)
    (a b : ℝ)
    (hd : ∀ w : ℂ, w.re ∈ Icc a b → DifferentiableAt ℂ regularized w)
    (heq : ∀ w : ℂ, w ≠ 1 → regularized w = density w * transform w)
    (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hgrowth : ∀ w : ℂ, w.re ∈ Icc a b → 1 ≤ |w.im| →
      ‖density w‖ ≤ D * (1 + |w.im|))
    (hdecay : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖transform (line x t)‖ ≤ B * (1 + |t|)⁻¹ ^ 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖regularized (line x t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2 := by
  apply uniform_vertical_decay_of_far_bound regularized a b hd (D * B) (mul_nonneg hD hB)
  intro x hx t ht
  have hre : (line x t).re ∈ Icc a b := by simpa [line] using hx
  have him : (line x t).im = t := by simp [line]
  have hne : line x t ≠ 1 := by
    intro h
    rw [show t = 0 from him.symm.trans (congrArg Complex.im h)] at ht
    norm_num at ht
  rw [heq _ hne, norm_mul]
  have hprod := mul_le_mul (hgrowth _ hre (by simpa only [him] using ht))
    (hdecay x hx t) (norm_nonneg _) (by positivity)
  rw [him] at hprod
  apply hprod.trans
  have hi : 0 ≤ (1 + |t|)⁻¹ := by positivity
  have hi1 : (1 + |t|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg t])
  have he : (D * (1 + |t|)) * (B * (1 + |t|)⁻¹ ^ 6) =
      (D * B) * (1 + |t|)⁻¹ ^ 5 := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hi hi1 (by norm_num)) (mul_nonneg hD hB)

/-- Integrability and contour shifting for a Mellin integrand with a removable
singularity. The original integrand agrees almost everywhere on the left line. -/
lemma verticalMellin_shift_of_ae_eq (regularized original : ℂ → ℂ) (a b C : ℝ)
    (hab : a ≤ b)
    (hd : ∀ w : ℂ, w.re ∈ Icc a b → DifferentiableAt ℂ regularized w)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖regularized (line x t)‖ ≤ C * (1 + |t|)⁻¹ ^ 2)
    (hae : (fun t : ℝ => regularized (line a t)) =ᵐ[volume] fun t => original (line a t)) :
    Integrable (fun t : ℝ => original (line a t)) ∧
      verticalMellin a original = verticalMellin b regularized := by
  have hint (x : ℝ) (hx : x ∈ Icc a b) :
      Integrable (fun t : ℝ => regularized (line x t)) := by
    apply integrable_of_uniform_vertical_decay _ x C
    · apply continuous_iff_continuousAt.mpr
      intro t
      exact (hd _ (by simpa [line] using hx)).continuousAt.comp (by unfold line; fun_prop)
    · exact hbound x hx
  refine ⟨(hint a ⟨le_rfl, hab⟩).congr hae, ?_⟩
  calc
    verticalMellin a original = verticalMellin a regularized := by
      unfold verticalMellin
      rw [integral_congr_ae hae.symm]
    _ = verticalMellin b regularized :=
      verticalMellin_eq_of_uniform_decay regularized a b C hab hd
        (hint a ⟨le_rfl, hab⟩) (hint b ⟨hab, le_rfl⟩) hbound

lemma regularizedModelMellin_uniform_decay (N : ℕ) (φ : ℝ → ℝ) (hφ : IsWeight φ)
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
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : 1 < b) (D : ℝ) (hD : 0 ≤ D)
    (hgrowth : ∀ w : ℂ, w.re ∈ Icc a b → 1 ≤ |w.im| →
      ‖continuedDensity N w‖ ≤ D * (1 + |w.im|)) :
    Integrable (fun t : ℝ => continuedDensity N (line a t) *
      mellin (fun y => (signedConvolution φ y : ℂ)) (line a t)) ∧
    verticalMellin a (fun w => continuedDensity N w *
      mellin (fun y => (signedConvolution φ y : ℂ)) w) =
      -(weightMass φ * singularSeries N : ℝ) := by
  obtain ⟨C, _, hbound⟩ := regularizedModelMellin_uniform_decay N φ hφ a b ha hab D hD hgrowth
  obtain ⟨hint, hshift⟩ := verticalMellin_shift_of_ae_eq (regularizedModelMellin N φ)
    (fun w => continuedDensity N w * mellin (fun y => (signedConvolution φ y : ℂ)) w)
    a b C hab
    (fun w hw => regularizedModelMellin_differentiableAt N φ hφ (ha.trans_le hw.1))
    hbound (regularizedModelMellin_line_ae N φ hφ a)
  exact ⟨hint, hshift.trans (regularizedModelMellin_initial N hN hpos φ hφ b hb).2⟩

end ConditionalGoldbach
