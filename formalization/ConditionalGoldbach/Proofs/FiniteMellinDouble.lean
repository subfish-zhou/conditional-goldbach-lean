import ConditionalGoldbach.Proofs.FiniteMellinProjection
import ConditionalGoldbach.Proofs.MellinMoment

/-! Absolutely convergent double Mellin inversion for a common sampling sequence. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma finite_double_mellin_inversion_series {ι : Type*} [Countable ι]
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (l r : ℝ)
    (hsupp : Function.support f ⊆ Icc l r) (σ : ℝ) (hσ : 0<σ) (u : ι → ℝ) (b : ι → ℂ)
    (hu : ∀ i, 0 < u i)
    (hb : Summable (fun i => ‖b i‖ * Real.rpow (u i) (-σ) ^ 2)) :
    Integrable (fun p : ℝ × ℝ => ∑' i,
      b i * (mellin (fun u => (f u:ℂ)) (line σ p.1) * (u i : ℂ) ^ (-line σ p.1)) *
        (mellin (fun u => (f u:ℂ)) (line σ p.2) * (u i : ℂ) ^ (-line σ p.2))) ∧
    HasSum (fun i => b i * (f (u i) : ℂ) ^ 2)
      (verticalMellin σ (fun s => verticalMellin σ (fun z => ∑' i,
        b i * (mellin (fun u => (f u:ℂ)) s * (u i : ℂ) ^ (-s)) *
          (mellin (fun u => (f u:ℂ)) z * (u i : ℂ) ^ (-z))))) := by
  let F : ι → ℝ × ℝ → ℂ := fun i p =>
    b i * (mellin (fun u => (f u:ℂ)) (line σ p.1) * (u i : ℂ) ^ (-line σ p.1)) *
      (mellin (fun u => (f u:ℂ)) (line σ p.2) * (u i : ℂ) ^ (-line σ p.2))
  let B : ι → ℝ × ℝ → ℝ := fun i p =>
    (‖b i‖ * Real.rpow (u i) (-σ) ^ 2) *
      (‖mellin (fun u => (f u:ℂ)) (line σ p.1)‖ * ‖mellin (fun u => (f u:ℂ)) (line σ p.2)‖)
  have hi (i : ι) : Integrable (F i) :=
    ((compact_mellin_finite_inversion_integrable f hf l r hsupp σ hσ (u i) (hu i)).const_mul (b i)).mul_prod
      (compact_mellin_finite_inversion_integrable f hf l r hsupp σ hσ (u i) (hu i))
  have heq (i : ι) (p : ℝ × ℝ) : ‖F i p‖ = B i p := by
    simp only [F, B, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp only [line, neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_self, add_zero, Real.rpow_eq_pow]
    ring
  have hBi : Integrable (fun p : ℝ × ℝ => ∑' i, B i p) := by
    simp only [B, tsum_mul_right]
    exact ((compact_mellin_finite_verticalIntegrable f hf l r hsupp σ hσ).norm.mul_prod
      (compact_mellin_finite_verticalIntegrable f hf l r hsupp σ hσ).norm).const_mul _
  have hsum : ∀ p : ℝ × ℝ, Summable (fun i => F i p) := by
    intro p
    apply Summable.of_norm
    simpa only [heq, B] using hb.mul_right
      (‖mellin (fun u => (f u:ℂ)) (line σ p.1)‖ * ‖mellin (fun u => (f u:ℂ)) (line σ p.2)‖)
  have hInt : Integrable (fun p : ℝ × ℝ => ∑' i, F i p) := by
    apply hBi.mono' (AEStronglyMeasurable.tsum (fun i => (hi i).aestronglyMeasurable))
    filter_upwards [] with p
    simpa only [heq] using norm_tsum_le_tsum_norm (hsum p).norm
  refine ⟨hInt, ?_⟩
  have h := hasSum_integral_of_dominated_convergence B
    (fun i => (hi i).aestronglyMeasurable)
    (fun i => Eventually.of_forall (fun p => (heq i p).le))
    (Eventually.of_forall (fun p => hb.mul_right _)) hBi
    (Eventually.of_forall (fun p => (hsum p).hasSum))
  let c : ℂ := (2 * (Real.pi : ℂ))⁻¹
  have hscaled := h.mul_left (c * c)
  convert hscaled using 1
  · ext i
    dsimp [F]
    rw [Measure.volume_eq_prod, integral_prod_mul
      (fun x : ℝ => b i * (mellin (fun u => (f u:ℂ)) (line σ x) * (u i : ℂ) ^ (-line σ x)))
      (fun y : ℝ => mellin (fun u => (f u:ℂ)) (line σ y) * (u i : ℂ) ^ (-line σ y)), integral_const_mul]
    rw [compact_mellin_finite_inversion f hf l r hsupp σ hσ (u i) (hu i)]
    unfold verticalMellin
    dsimp [c]
    ring
  · rw [Measure.volume_eq_prod, integral_prod _ hInt]
    simp only [verticalMellin, integral_const_mul]
    dsimp [c, F]
    ring

end ConditionalGoldbach
