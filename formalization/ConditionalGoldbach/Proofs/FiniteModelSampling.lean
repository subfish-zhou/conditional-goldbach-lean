import ConditionalGoldbach.Proofs.FiniteModelConvolution
import ConditionalGoldbach.Proofs.MellinModelSampling

/-! C6 Mellin sampling with the nonsymmetric cross mass. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach.FiniteModel

lemma signedConvolution_mellin_decay (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃ C : ℝ, 0<C ∧ ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖mellin (fun u => (signedConvolution φ u : ℂ)) (line x t)‖ ≤ C*(1+|t|)⁻¹^6 := by
  obtain ⟨C,hC,hbound⟩ := compact_mellin_finite_decay 6 (signedConvolution φ)
    (signedConvolution_contDiff φ hφ) _ _ (signedConvolution_support φ hφ) a b ha hab
  refine ⟨C,hC,fun x hx t => ?_⟩
  simpa [line] using hbound (line x t) (by simpa [line] using hx)

lemma signedConvolution_integer_sample (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    (∑' k : ℕ, (singularSeries ((k + 1) * N) : ℂ) * (signedConvolution φ (k + 1 : ℕ) : ℂ)) =
      -(modelMass φ * singularSeries N : ℝ) := by
  rw [tsum_eq_single 0]
  · simp only [zero_add, one_mul, Nat.cast_one, (convolution_integer_values φ hφ).2.2, ofReal_neg,
      ofReal_mul]
    ring
  · intro k hk
    have hC := (convolution_integer_values φ hφ).1 (k + 1) (by omega)
    have hJ := (convolution_integer_values φ hφ).2.1 (k + 1) (by omega)
    simp only [signedConvolution, hC, hJ, mul_zero, sub_self, ofReal_zero]

lemma density_signedConvolution_mellin_initial (N : ℕ) (hN : Even N) (hNpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun t : ℝ => densitySeries N (line σ t) *
      mellin (fun y => (signedConvolution φ y : ℂ)) (line σ t)) ∧
    verticalMellin σ (fun s => densitySeries N s * mellin (fun y => (signedConvolution φ y : ℂ)) s) =
      -(modelMass φ * singularSeries N : ℝ) := by
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hb := density_sampling_coeff_summable N hN hNpos σ hσ
  have hi := finite_mellin_inversion_sum_integrable (signedConvolution φ)
    ((signedConvolution_contDiff φ hφ).of_le (by norm_num)) (hφ.lower-hφ.upper) (2*hφ.upper)
    (signedConvolution_support φ hφ) σ hσ0
    (fun k : ℕ => (k + 1 : ℕ)) (fun k => (singularSeries ((k + 1) * N) : ℂ))
    (fun k => by positivity) hb
  have hv := finite_mellin_inversion_hasSum (signedConvolution φ)
    ((signedConvolution_contDiff φ hφ).of_le (by norm_num)) (hφ.lower-hφ.upper) (2*hφ.upper)
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

end ConditionalGoldbach.FiniteModel
