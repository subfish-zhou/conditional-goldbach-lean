module

public import ConditionalGoldbach.Proofs.MellinCompactPositive
public import ConditionalGoldbach.Proofs.DensityConvergence

/-! Mellin sampling of the signed convolution on an absolutely convergent density line. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

theorem compact_mellin_inversion_hasSum {ι : Type*} [Countable ι]
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (σ : ℝ) (hσ : 0 < σ) (u : ι → ℝ) (b : ι → ℂ)
    (hu : ∀ i, 0 < u i)
    (hb : Summable (fun i => ‖b i‖ * Real.rpow (u i) (-σ))) :
    HasSum (fun i => b i * (f (u i) : ℂ))
      (verticalMellin σ (fun s => ∑' i, b i * mellin (fun y => (f y : ℂ)) s * (u i : ℂ) ^ (-s))) := by
  let F : ι → ℝ → ℂ := fun i t =>
    b i * mellin (fun y => (f y : ℂ)) (line σ t) * (u i : ℂ) ^ (-line σ t)
  let Majorant : ι → ℝ → ℝ := fun i t =>
    (‖b i‖ * Real.rpow (u i) (-σ)) * ‖mellin (fun y => (f y : ℂ)) (line σ t)‖
  have hint (i : ι) : Integrable (F i) := by
    simpa only [F, mul_assoc] using
      (compact_mellin_inversion_integrable f hf A B hsupp σ hσ (u i) (hu i)).const_mul (b i)
  have heq (i : ι) (t : ℝ) : ‖F i t‖ = Majorant i t := by
    simp only [F, Majorant, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp only [line, neg_re, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
    rw [Real.rpow_eq_pow]
    ring
  have hBi : Integrable (fun t => ∑' i, Majorant i t) := by
    simp only [Majorant, tsum_mul_right]
    exact (compact_mellin_verticalIntegrable f hf A B hsupp σ hσ).norm.const_mul _
  have h := hasSum_integral_of_dominated_convergence Majorant
    (fun i => (hint i).aestronglyMeasurable)
    (fun i => Eventually.of_forall (fun t => (heq i t).le))
    (Eventually.of_forall (fun t => hb.mul_right _)) hBi
    (Eventually.of_forall (fun t =>
      (Summable.of_norm (by simpa only [heq] using hb.mul_right ‖mellin (fun y => (f y : ℂ)) (line σ t)‖)).hasSum))
  have hscaled := h.mul_left ((2 * (Real.pi : ℂ))⁻¹)
  convert hscaled using 1
  · ext i
    rw [compact_mellin_inversion f hf A B hsupp σ hσ (u i) (hu i)]
    simp only [verticalMellin, F, mul_assoc, integral_const_mul]
    ring
  · rfl



theorem compact_mellin_inversion_sum_integrable {ι : Type*} [Countable ι]
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (σ : ℝ) (hσ : 0 < σ) (u : ι → ℝ) (b : ι → ℂ)
    (hu : ∀ i, 0 < u i)
    (hb : Summable (fun i => ‖b i‖ * Real.rpow (u i) (-σ))) :
    Integrable (fun t : ℝ => ∑' i,
      b i * mellin (fun y => (f y : ℂ)) (line σ t) * (u i : ℂ) ^ (-line σ t)) := by
  let F : ι → ℝ → ℂ := fun i t =>
    b i * mellin (fun y => (f y : ℂ)) (line σ t) * (u i : ℂ) ^ (-line σ t)
  have hint (i : ι) : Integrable (F i) := by
    simpa only [F, mul_assoc] using
      (compact_mellin_inversion_integrable f hf A B hsupp σ hσ (u i) (hu i)).const_mul (b i)
  have hnorm (i : ι) (t : ℝ) : ‖F i t‖ =
      (‖b i‖ * Real.rpow (u i) (-σ)) * ‖mellin (fun y => (f y : ℂ)) (line σ t)‖ := by
    simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu i)]
    simp only [line, neg_re, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, Real.rpow_eq_pow]
    ring
  apply ((compact_mellin_verticalIntegrable f hf A B hsupp σ hσ).norm.const_mul
    (∑' i, ‖b i‖ * Real.rpow (u i) (-σ))).mono'
    (AEStronglyMeasurable.tsum (fun i => (hint i).aestronglyMeasurable))
  filter_upwards [] with t
  have hs : Summable (fun i => ‖F i t‖) := by
    simpa only [hnorm] using hb.mul_right ‖mellin (fun y => (f y : ℂ)) (line σ t)‖
  calc
    ‖∑' i, F i t‖ ≤ ∑' i, ‖F i t‖ := norm_tsum_le_tsum_norm hs
    _ = _ := by simp only [hnorm, tsum_mul_right, line]


lemma density_sampling_coeff_summable (N : ℕ) (hN : Even N) (hNpos : 0 < N)
    (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun k : ℕ => ‖(singularSeries ((k + 1) * N) : ℂ)‖ *
      Real.rpow (k + 1 : ℕ) (-σ)) := by
  have hs := (summable_nat_add_iff 1).2 (densitySeries_summable_norm N hN hNpos (w := (σ : ℂ)) hσ)
  apply hs.congr
  intro k
  simp only [Nat.succ_pos, ite_true, norm_div, Complex.norm_natCast_cpow_of_pos (by omega : 0 < k + 1), ofReal_re]
  rw [Real.rpow_eq_pow, Real.rpow_neg (by positivity)]
  rfl

lemma densitySeries_shifted (N : ℕ) (hN : Even N) (hNpos : 0 < N) (s : ℂ) (hs : 1 < s.re) :
    densitySeries N s = ∑' k : ℕ, (singularSeries ((k + 1) * N) : ℂ) / (k + 1 : ℕ) ^ s := by
  have hsum : Summable (fun k : ℕ => if 0 < k then (singularSeries (k * N) : ℂ) / (k : ℂ) ^ s else 0) := by
    apply Summable.of_norm
    simpa only [apply_ite norm, norm_zero] using densitySeries_summable_norm N hN hNpos hs
  unfold densitySeries
  rw [hsum.tsum_eq_zero_add]
  simp

lemma density_mellin_integrand_series (N : ℕ) (hN : Even N) (hNpos : 0 < N)
    (f : ℝ → ℝ) (s : ℂ) (hs : 1 < s.re) :
    (∑' k : ℕ, (singularSeries ((k + 1) * N) : ℂ) * mellin (fun y => (f y : ℂ)) s *
      (k + 1 : ℕ) ^ (-s)) = densitySeries N s * mellin (fun y => (f y : ℂ)) s := by
  rw [densitySeries_shifted N hN hNpos s hs, ← tsum_mul_right]
  apply tsum_congr
  intro k
  rw [cpow_neg]
  ring

lemma signedConvolution_integer_sample (N : ℕ) (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∑' k : ℕ, (singularSeries ((k + 1) * N) : ℂ) * (signedConvolution φ (k + 1 : ℕ) : ℂ)) =
      -(weightMass φ * singularSeries N : ℝ) := by
  rw [tsum_eq_single 0]
  · simp only [zero_add, one_mul, Nat.cast_one, (convolution_integer_values φ hφ).2.2, ofReal_neg,
      ofReal_mul]
    ring
  · intro k hk
    have hC := (convolution_integer_values φ hφ).1 (k + 1) (by omega)
    have hJ := (convolution_integer_values φ hφ).2.1 (k + 1) (by omega)
    simp only [signedConvolution, hC, hJ, mul_zero, sub_self, ofReal_zero]

lemma density_signedConvolution_mellin_initial (N : ℕ) (hN : Even N) (hNpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => densitySeries N (line σ t) *
      mellin (fun y => (signedConvolution φ y : ℂ)) (line σ t)) ∧
    verticalMellin σ (fun s => densitySeries N s * mellin (fun y => (signedConvolution φ y : ℂ)) s) =
      -(weightMass φ * singularSeries N : ℝ) := by
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hb := density_sampling_coeff_summable N hN hNpos σ hσ
  have hi := compact_mellin_inversion_sum_integrable (signedConvolution φ)
    (signedConvolution_contDiff φ hφ) (-(1 / 3)) (4 / 3)
    (signedConvolution_support φ hφ) σ hσ0
    (fun k : ℕ => (k + 1 : ℕ)) (fun k => (singularSeries ((k + 1) * N) : ℂ))
    (fun k => by positivity) hb
  have hv := compact_mellin_inversion_hasSum (signedConvolution φ)
    (signedConvolution_contDiff φ hφ) (-(1 / 3)) (4 / 3)
    (signedConvolution_support φ hφ) σ hσ0
    (fun k : ℕ => (k + 1 : ℕ)) (fun k => (singularSeries ((k + 1) * N) : ℂ))
    (fun k => by positivity) hb
  constructor
  · apply hi.congr
    filter_upwards [] with t
    simpa only [Complex.ofReal_natCast] using density_mellin_integrand_series N hN hNpos
      (signedConvolution φ) (line σ t) (by simpa [line] using hσ)
  · rw [← signedConvolution_integer_sample N φ hφ, hv.tsum_eq]
    unfold verticalMellin
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    exact (density_mellin_integrand_series N hN hNpos (signedConvolution φ) (line σ t)
      (by simpa [line] using hσ)).symm

end ConditionalGoldbach
