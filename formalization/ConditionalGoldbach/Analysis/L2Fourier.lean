module

public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Fourier integrals and physical normalization on L²(ℝ, ℂ)

This module depends only on Mathlib. It relates the classical Fourier integral
and the L² Fourier isometry, realizes nonzero real dilations in L², and proves
continuity and norm preservation for the physical normalization. Hardy interior
restrictions and endpoint traces are independent consumers of these facts.
-/
@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform SchwartzMap
open scoped ContDiff Topology
namespace ConditionalGoldbach.Analysis

/-- The classical Fourier transform of an integrable function is continuous. -/
lemma classical_fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f)
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (show Continuous (fun p : ℝ × ℝ => inner ℝ p.1 p.2) from continuous_inner) hf)

/-- Pairing the Fourier transform with a Schwartz test function commutes with Fourier transform. -/
lemma classical_fourier_integral_test {f : ℝ → ℂ} (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, g t * 𝓕 f t) = ∫ t : ℝ, 𝓕 g t * f t := by
  simpa only [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral, smul_eq_mul, innerₗ_apply_apply,
    LinearMap.flip_apply, real_inner_comm, mul_comm] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf (g.integrable (μ := volume)))

/-- For an integrable L² function, the classical and L² Fourier transforms agree almost everywhere. -/
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

/-- The classical Fourier transform of an integrable L² function lies in L². -/
lemma classical_fourier_memLp {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  MemLp.ae_eq (classical_fourier_eq_L2_ae hf hf2).symm (Lp.memLp _)

/-- A nonzero real dilation preserves membership in L². -/
lemma memLp_comp_real_mul {f : ℝ → ℂ} (hf : MemLp f 2) {c : ℝ} (hc : c ≠ 0) :
    MemLp (fun t : ℝ => f (c * t)) 2 := by
  have hm : MemLp f 2 (Measure.map (fun t : ℝ => c * t) volume) := by
    rw [Real.map_volume_mul_left hc]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (by fun_prop)

/-- The pushforward of Lebesgue measure under multiplication by a nonzero real scalar. -/
def realScaleMeasure (c : ℝ) : Measure ℝ := ENNReal.ofReal |c⁻¹| • volume

/-- Multiplication by a nonzero scalar preserves the appropriately rescaled measure. -/
lemma realScale_measurePreserving {c : ℝ} (hc : c ≠ 0) :
    MeasurePreserving (fun t : ℝ => c * t) volume (realScaleMeasure c) :=
  ⟨by fun_prop, Real.map_volume_mul_left hc⟩

/-- Real dilation on L², realized through the pushforward measure rather than representatives. -/
def rescaleL2 (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun t : ℝ => c * t) (realScale_measurePreserving hc)
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (show realScaleMeasure c ≤ ENNReal.ofReal |c⁻¹| • volume from le_rfl) f)

/-- The L² dilation is continuous in its function argument. -/
lemma rescaleL2_continuous (c : ℝ) (hc : c ≠ 0) : Continuous (rescaleL2 c hc) :=
  (Lp.isometry_compMeasurePreserving (E := ℂ) (p := 2)
    (realScale_measurePreserving hc)).continuous.comp
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (show realScaleMeasure c ≤ ENNReal.ofReal |c⁻¹| • volume from le_rfl)).continuous

/-- The L² dilation agrees almost everywhere with dilation of representatives. -/
lemma rescaleL2_coe (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleL2 c hc f =ᵐ[volume] (fun t => f (c * t)) := by
  refine (Lp.coeFn_compMeasurePreserving _ (realScale_measurePreserving hc)).trans ?_
  exact (realScale_measurePreserving hc).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (show realScaleMeasure c ≤ ENNReal.ofReal |c⁻¹| • volume from le_rfl) f)

/-- The physical Fourier normalization: (2π)⁻¹ᐟ² times the transform at −t/(2π). -/
def physicalFourierL2 (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
    rescaleL2 (-(2 * Real.pi)⁻¹)
      (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))) (𝓕 f)

/-- Continuity of the physically normalized Fourier transform on L². -/
lemma physicalFourierL2_continuous : Continuous physicalFourierL2 := by
  unfold physicalFourierL2
  exact ((rescaleL2_continuous (-(2 * Real.pi)⁻¹) _).comp
    (continuous_fourier : Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => 𝓕 f))).const_smul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)

/-- The squared L² norm equals the integral of the squared representative norm. -/
lemma L2_norm_sq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ t : ℝ, ‖f t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The L² norm of a `MemLp.toLp` representative is the square root of its energy. -/
lemma toLp_norm_eq_sqrt_integral {f : ℝ → ℂ} (hf : MemLp f 2) :
    ‖hf.toLp f‖ = Real.sqrt (∫ t : ℝ, ‖f t‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (hf.toLp f)), L2_norm_sq_integral]
  congr 1
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖ ^ 2))

/-- The physical L² transform has the expected classical integral representative. -/
lemma physicalFourierL2_coe_classical {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    physicalFourierL2 (hf2.toLp f) =ᵐ[volume] (fun t : ℝ =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * 𝓕 f (-t / (2 * Real.pi))) := by
  let c : ℝ := -(2 * Real.pi)⁻¹
  have hc : c ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hq : QuasiMeasurePreserving (fun t : ℝ => c * t) volume volume :=
    (realScale_measurePreserving hc).quasiMeasurePreserving.mono_right Measure.smul_absolutelyContinuous
  have he := hq.ae_eq_comp (classical_fourier_eq_L2_ae hf hf2)
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)
    (rescaleL2 c hc (𝓕 (hf2.toLp f))), rescaleL2_coe c hc (𝓕 (hf2.toLp f)), he] with t ht hr he
  change (_ • rescaleL2 c hc (𝓕 (hf2.toLp f))) t = _
  rw [ht]
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hr he ⊢
  rw [hr, ← he]
  congr 2
  dsimp [c]
  ring_nf

/-- A real dilation scales squared L² norm by the absolute inverse dilation factor. -/
lemma rescaleL2_norm_sq (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖rescaleL2 c hc f‖ ^ 2 = |c⁻¹| * ‖f‖ ^ 2 := by
  rw [L2_norm_sq_integral]
  calc
    _ = ∫ t : ℝ, ‖f (c * t)‖ ^ 2 :=
      integral_congr_ae ((rescaleL2_coe c hc f).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    _ = |c⁻¹| * ∫ t : ℝ, ‖f t‖ ^ 2 := by
      simpa only [smul_eq_mul] using (Measure.integral_comp_mul_left (fun t : ℝ => ‖f t‖ ^ 2) c)
    _ = _ := by rw [← L2_norm_sq_integral]

/-- The physical Fourier normalization preserves the squared L² norm. -/
lemma physicalFourierL2_norm_sq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖physicalFourierL2 f‖ ^ 2 = ‖f‖ ^ 2 := by
  unfold physicalFourierL2
  rw [norm_smul, mul_pow, rescaleL2_norm_sq, Lp.norm_fourier_eq]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), inv_neg, inv_inv,
    abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp

end ConditionalGoldbach.Analysis
