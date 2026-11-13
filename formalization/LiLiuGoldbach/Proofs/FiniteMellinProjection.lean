import LiLiuGoldbach.Proofs.FiniteMellin
import LiLiuGoldbach.Proofs.MellinProjection

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

theorem finite_mellin_inversion_hasSum {ι : Type*} [Countable ι]
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (l r : ℝ) (hsupp : Function.support f ⊆ Icc l r) (σ : ℝ) (hσ : 0<σ) (u : ι → ℝ) (b : ι → ℂ)
    (hu : ∀ i, 0 < u i)
    (hb : Summable (fun i => ‖b i‖ * Real.rpow (u i) (-σ))) :
    HasSum (fun i => b i * (f (u i) : ℂ))
      (verticalMellin σ (fun s => ∑' i, b i * mellin (fun u => (f u:ℂ)) s * (u i : ℂ) ^ (-s))) := by
  let F : ι → ℝ → ℂ := fun i t =>
    b i * mellin (fun u => (f u:ℂ)) (line σ t) * (u i : ℂ) ^ (-line σ t)
  let B : ι → ℝ → ℝ := fun i t =>
    (‖b i‖ * Real.rpow (u i) (-σ)) * ‖mellin (fun u => (f u:ℂ)) (line σ t)‖
  have hint (i : ι) : Integrable (F i) := by
    simpa only [F, mul_assoc] using
      (compact_mellin_finite_inversion_integrable f hf l r hsupp σ hσ (u i) (hu i)).const_mul (b i)
  have heq (i : ι) (t : ℝ) : ‖F i t‖ = B i t := by
    simp only [F, B, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp only [line, neg_re, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
    rw [Real.rpow_eq_pow]
    ring
  have hBi : Integrable (fun t => ∑' i, B i t) := by
    simp only [B, tsum_mul_right]
    exact (compact_mellin_finite_verticalIntegrable f hf l r hsupp σ hσ).norm.const_mul _
  have h := hasSum_integral_of_dominated_convergence B
    (fun i => (hint i).aestronglyMeasurable)
    (fun i => Eventually.of_forall (fun t => (heq i t).le))
    (Eventually.of_forall (fun t => hb.mul_right _)) hBi
    (Eventually.of_forall (fun t =>
      (Summable.of_norm (by simpa only [heq] using hb.mul_right ‖mellin (fun u => (f u:ℂ)) (line σ t)‖)).hasSum))
  have hscaled := h.mul_left ((2 * (Real.pi : ℂ))⁻¹)
  convert hscaled using 1
  · ext i
    rw [compact_mellin_finite_inversion f hf l r hsupp σ hσ (u i) (hu i)]
    simp only [verticalMellin, F, mul_assoc, integral_const_mul]
    ring
  · rfl



theorem finite_mellin_inversion_sum_integrable {ι : Type*} [Countable ι]
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (l r : ℝ) (hsupp : Function.support f ⊆ Icc l r) (σ : ℝ) (hσ : 0<σ) (u : ι → ℝ) (b : ι → ℂ)
    (hu : ∀ i, 0 < u i)
    (hb : Summable (fun i => ‖b i‖ * Real.rpow (u i) (-σ))) :
    Integrable (fun t : ℝ => ∑' i,
      b i * mellin (fun u => (f u:ℂ)) (line σ t) * (u i : ℂ) ^ (-line σ t)) := by
  let F : ι → ℝ → ℂ := fun i t =>
    b i * mellin (fun u => (f u:ℂ)) (line σ t) * (u i : ℂ) ^ (-line σ t)
  have hint (i : ι) : Integrable (F i) := by
    simpa only [F, mul_assoc] using
      (compact_mellin_finite_inversion_integrable f hf l r hsupp σ hσ (u i) (hu i)).const_mul (b i)
  have hnorm (i : ι) (t : ℝ) : ‖F i t‖ =
      (‖b i‖ * Real.rpow (u i) (-σ)) * ‖mellin (fun u => (f u:ℂ)) (line σ t)‖ := by
    simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp only [line, neg_re, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, Real.rpow_eq_pow]
    ring
  apply ((compact_mellin_finite_verticalIntegrable f hf l r hsupp σ hσ).norm.const_mul
    (∑' i, ‖b i‖ * Real.rpow (u i) (-σ))).mono'
    (AEStronglyMeasurable.tsum (fun i => (hint i).aestronglyMeasurable))
  filter_upwards [] with t
  have hs : Summable (fun i => ‖F i t‖) := by
    simpa only [hnorm] using hb.mul_right ‖mellin (fun u => (f u:ℂ)) (line σ t)‖
  calc
    ‖∑' i, F i t‖ ≤ ∑' i, ‖F i t‖ := norm_tsum_le_tsum_norm hs
    _ = _ := by simp only [hnorm, tsum_mul_right, line]


lemma finite_character_mellin_series {N : ℕ} [NeZero N] (χ : Character N)
    (f : ℝ → ℝ) (s : ℂ) (hs : 1 / 2 < s.re) :
    (∑' n : ℕ, ((mangoldt (n + 1) : ℂ) * χ (n + 1) /
      (n + 1 : ℕ) ^ (1 / 2 : ℂ)) * mellin (fun u => (f u:ℂ)) s *
      (((n + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-s)) =
      -((N : ℂ) ^ s * mellin (fun u => (f u:ℂ)) s * logDerivative χ s) := by
  rw [logDerivative_eq_neg_tsum χ hs, mul_neg, neg_neg,
    (summable_logDerivative_terms χ hs).tsum_eq_zero_add]
  simp only [mangoldt, ArithmeticFunction.map_zero,
    Complex.ofReal_zero, zero_mul, zero_div, zero_add]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  calc
    _ = mellin (fun u => (f u:ℂ)) s *
        (((mangoldt (n + 1) : ℂ) * χ (n + 1) /
          (n + 1 : ℕ) ^ (1 / 2 : ℂ)) *
          (((n + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-s)) := by ring
    _ = _ := by
      rw [mellin_dirichlet_rescale (n + 1) N (by omega) (NeZero.pos _)]
      push_cast
      ring

lemma finite_character_mellin_initial_integrable {N : ℕ} [NeZero N]
    (χ : Character N) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (l r : ℝ)
    (hsupp : Function.support f ⊆ Icc l r) (σ : ℝ) (hσ : 1/2<σ) :
    Integrable (fun t : ℝ => (N:ℂ)^(line σ t)*mellin (fun u => (f u:ℂ)) (line σ t)*logDerivative χ (line σ t)) := by
  have hint := finite_mellin_inversion_sum_integrable f hf l r hsupp σ (by linarith)
    (fun n : ℕ => (n+1:ℕ)/(N:ℝ))
    (fun n : ℕ => (mangoldt (n+1):ℂ)*χ (n+1)/(n+1:ℕ)^(1/2:ℂ))
    (fun n => by have := NeZero.pos N; positivity) (character_mellin_coeff_summable χ σ hσ)
  convert hint.neg using 1
  ext t
  simp only [Pi.neg_apply]
  rw [finite_character_mellin_series χ f (line σ t) (by simpa [line] using hσ),neg_neg]

end LiLiuGoldbach16
