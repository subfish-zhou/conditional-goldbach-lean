import LiLiuGoldbach.BaseDefinitions

/-! Compatibility of the classical Fourier integral with the `L²` Fourier isometry.
This supplies the analytic interface needed for the Hardy-strip construction. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform SchwartzMap
open scoped ContDiff
namespace LiLiuGoldbach16

lemma classical_fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f)
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (show Continuous (fun p : ℝ × ℝ => inner ℝ p.1 p.2) from continuous_inner) hf)

lemma classical_fourier_integral_test {f : ℝ → ℂ} (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, g t * 𝓕 f t) = ∫ t : ℝ, 𝓕 g t * f t := by
  simpa only [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral, smul_eq_mul, innerₗ_apply_apply,
    LinearMap.flip_apply, real_inner_comm, mul_comm] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf (g.integrable (μ := volume)))

lemma classical_fourier_eq_L2_ae {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 (hf2.toLp f) : Lp ℂ 2) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (classical_fourier_continuous hf).locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg'
  have h := congrArg (fun D : 𝓢'(ℝ, ℂ) => D G)
    (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  have heq : (∫ t : ℝ, 𝓕 G t * f t) =
      ∫ t : ℝ, 𝓕 G t * (hf2.toLp f) t := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with t ht
    rw [ht]
  calc
    _ = ∫ t : ℝ, G t * 𝓕 f t := by simp [G, Complex.real_smul]
    _ = ∫ t : ℝ, 𝓕 G t * f t := classical_fourier_integral_test hf G
    _ = ∫ t : ℝ, 𝓕 G t * (hf2.toLp f) t := heq
    _ = _ := by simpa [Lp.toTemperedDistribution_apply, smul_eq_mul,
      TemperedDistribution.fourier_apply, G, Complex.real_smul] using h

lemma classical_fourier_memLp {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  MemLp.ae_eq (classical_fourier_eq_L2_ae hf hf2).symm (Lp.memLp _)


lemma memLp_comp_real_mul {f : ℝ → ℂ} (hf : MemLp f 2) {c : ℝ} (hc : c ≠ 0) :
    MemLp (fun t : ℝ => f (c * t)) 2 := by
  have hm : MemLp f 2 (Measure.map (fun t : ℝ => c * t) volume) := by
    rw [Real.map_volume_mul_left hc]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (by fun_prop)

end LiLiuGoldbach16
