module

public import ConditionalGoldbach.Analysis.L2Fourier

/-! Compatibility names for the shared L² Fourier interface. -/
public section

noncomputable section
open MeasureTheory FourierTransform SchwartzMap
namespace ConditionalGoldbach

lemma classical_fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  Analysis.classical_fourier_continuous hf

lemma classical_fourier_integral_test {f : ℝ → ℂ} (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, g t * 𝓕 f t) = ∫ t : ℝ, 𝓕 g t * f t :=
  Analysis.classical_fourier_integral_test hf g

lemma classical_fourier_eq_L2_ae {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 (hf2.toLp f) : Lp ℂ 2) :=
  Analysis.classical_fourier_eq_L2_ae hf hf2

lemma classical_fourier_memLp {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  Analysis.classical_fourier_memLp hf hf2

lemma memLp_comp_real_mul {f : ℝ → ℂ} (hf : MemLp f 2) {c : ℝ} (hc : c ≠ 0) :
    MemLp (fun t : ℝ => f (c * t)) 2 :=
  Analysis.memLp_comp_real_mul hf hc

end ConditionalGoldbach
