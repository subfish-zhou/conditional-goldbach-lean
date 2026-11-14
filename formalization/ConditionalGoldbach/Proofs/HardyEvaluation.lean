module

public import ConditionalGoldbach.Definitions.Operators
public import ConditionalGoldbach.Proofs.HardyRawNorm

/-! Evaluation vectors in the weighted Fourier realization of the strip Hardy space. -/
@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma hardy_evaluation_quotient_le (a b x c τ : ℝ) (hc : c = a ∨ c = b) :
    Real.exp (2 * x * τ) / hardyWeight a b τ ≤ Real.exp (2 * (x - c) * τ) := by
  apply (div_le_iff₀ (hardyWeight_pos a b τ)).mpr
  have he : Real.exp (2 * x * τ) =
      Real.exp (2 * (x - c) * τ) * Real.exp (2 * c * τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rcases hc with rfl | rfl
  · exact le_add_of_nonneg_right (Real.exp_pos _).le
  · exact le_add_of_nonneg_left (Real.exp_pos _).le

lemma hardy_evaluation_quotient_integrable {a b x : ℝ} (hx : x ∈ Ioo a b) :
    Integrable (fun τ : ℝ => Real.exp (2 * x * τ) / hardyWeight a b τ) := by
  have hm : Continuous (fun τ : ℝ => Real.exp (2 * x * τ) / hardyWeight a b τ) :=
    (by fun_prop : Continuous (fun τ : ℝ => Real.exp (2 * x * τ))).div (hardyWeight_continuous a b) (fun τ => (hardyWeight_pos a b τ).ne')
  have hl : IntegrableOn (fun τ : ℝ => Real.exp (2 * x * τ) / hardyWeight a b τ) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic (show 0 < 2 * (x - a) by linarith [hx.1]) 0).mono'
      hm.aestronglyMeasurable
    filter_upwards [] with τ
    simpa only [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (hardyWeight_pos a b τ))]
      using hardy_evaluation_quotient_le a b x a τ (Or.inl rfl)
  have hr : IntegrableOn (fun τ : ℝ => Real.exp (2 * x * τ) / hardyWeight a b τ) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (show 2 * (x - b) < 0 by linarith [hx.2]) 0).mono'
      hm.aestronglyMeasurable
    filter_upwards [] with τ
    simpa only [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (hardyWeight_pos a b τ))]
      using hardy_evaluation_quotient_le a b x b τ (Or.inr rfl)
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

/-- The unnormalized density of an evaluation vector; normalization is applied as a scalar. -/
def hardyEvaluationDensity (a b : ℝ) (s : ℂ) (τ : ℝ) : ℂ :=
  Complex.exp (conj s * τ) / (hardyWeight a b τ : ℂ)

lemma hardyEvaluationDensity_continuous (a b : ℝ) (s : ℂ) :
    Continuous (hardyEvaluationDensity a b s) := by
  unfold hardyEvaluationDensity
  apply (by fun_prop : Continuous (fun τ : ℝ => Complex.exp (conj s * τ))).div
    (Complex.continuous_ofReal.comp (hardyWeight_continuous a b))
  intro τ
  exact Complex.ofReal_ne_zero.mpr (hardyWeight_pos a b τ).ne'

lemma hardyEvaluationDensity_weighted_norm_sq (a b : ℝ) (s : ℂ) (τ : ℝ) :
    ‖hardyEvaluationDensity a b s τ‖ ^ 2 * hardyWeight a b τ =
      Real.exp (2 * s.re * τ) / hardyWeight a b τ := by
  simp only [hardyEvaluationDensity, norm_div, Complex.norm_exp, Complex.mul_re,
    Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hardyWeight_pos a b τ), div_pow]
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * (s.re * τ) = 2 * s.re * τ by ring]
  field_simp

lemma hardyEvaluationDensity_memLp {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b) :
    MemLp (hardyEvaluationDensity a b s) 2 (hardyMeasure a b) := by
  apply (memLp_two_iff_integrable_sq_norm (hardyEvaluationDensity_continuous a b s).aestronglyMeasurable).mpr
  change Integrable _ (volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ)))
  rw [integrable_withDensity_iff (hardyWeight_continuous a b).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (hardyWeight_pos a b _).le, smul_eq_mul,
    mul_comm (hardyWeight a b _) _, hardyEvaluationDensity_weighted_norm_sq] using
    hardy_evaluation_quotient_integrable hs

lemma hardyEvaluationDensity_pairing {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b)
    (ψ : HardySpace a b) :
    paperInner ψ ((hardyEvaluationDensity_memLp hs).toLp _) =
      ∫ τ : ℝ, ψ τ * Complex.exp (s * τ) := by
  unfold paperInner
  rw [L2.inner_def]
  calc
    (∫ τ : ℝ, inner ℂ (((hardyEvaluationDensity_memLp hs).toLp _) τ) (ψ τ)
      ∂hardyMeasure a b) =
        ∫ τ : ℝ, ψ τ * (Complex.exp (s * τ) / (hardyWeight a b τ : ℂ)) ∂hardyMeasure a b := by
      apply integral_congr_ae
      filter_upwards [(hardyEvaluationDensity_memLp hs).coeFn_toLp] with τ hτ
      rw [hτ]
      simp only [RCLike.inner_apply, hardyEvaluationDensity, map_div₀, ← Complex.exp_conj,
        map_mul, Complex.conj_conj, Complex.conj_ofReal]
    _ = _ := by
      change (∫ τ : ℝ, ψ τ * (Complex.exp (s * τ) / (hardyWeight a b τ : ℂ))
        ∂(volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ)))) = _
      rw [integral_withDensity_eq_integral_toReal_smul
        (hardyWeight_continuous a b).measurable.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with τ
      simp only [ENNReal.toReal_ofReal (hardyWeight_pos a b τ).le, Complex.real_smul]
      have hw : (hardyWeight a b τ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (hardyWeight_pos a b τ).ne'
      field_simp

lemma evaluationVector_exists {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b) :
    ∃ v : HardySpace a b, ∀ ψ, fourierLaplace ψ s = paperInner ψ v := by
  refine ⟨(Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • (hardyEvaluationDensity_memLp hs).toLp _, ?_⟩
  intro ψ
  rw [paperInner, inner_smul_left]
  change _ = _ * paperInner ψ ((hardyEvaluationDensity_memLp hs).toLp _)
  rw [hardyEvaluationDensity_pairing hs]
  simp only [map_inv₀, Complex.conj_ofReal, fourierLaplace]

lemma evaluationVector_spec {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b)
    (ψ : HardySpace a b) : fourierLaplace ψ s = paperInner ψ (evaluationVector s) := by
  have h := evaluationVector_exists hs
  unfold evaluationVector
  rw [dite_eq_left h]
  exact Classical.choose_spec h ψ

lemma evaluationVector_eq_density {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b) :
    (evaluationVector s : HardySpace a b) =
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • (hardyEvaluationDensity_memLp hs).toLp _ := by
  apply ext_inner_right ℂ
  intro ψ
  change paperInner ψ (evaluationVector s) = _
  rw [← evaluationVector_spec hs]
  change fourierLaplace ψ s = inner ℂ (_ • _) ψ
  rw [inner_smul_left]
  change _ = _ * paperInner ψ ((hardyEvaluationDensity_memLp hs).toLp _)
  rw [hardyEvaluationDensity_pairing hs]
  simp only [map_inv₀, Complex.conj_ofReal, fourierLaplace]

lemma evaluationVector_norm_sq_integral {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b) :
    ‖(evaluationVector s : HardySpace a b)‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ τ : ℝ, Real.exp (2 * s.re * τ) / hardyWeight a b τ := by
  rw [evaluationVector_eq_density hs, norm_smul, mul_pow]
  have hc : ‖(Real.sqrt (2 * Real.pi) : ℂ)⁻¹‖ ^ 2 = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by positivity)]
  rw [hc, hardySpace_norm_sq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [(volume_absolutelyContinuous_hardyMeasure a b).ae_eq
    (hardyEvaluationDensity_memLp hs).coeFn_toLp] with τ hτ
  rw [hτ, hardyEvaluationDensity_weighted_norm_sq]

lemma norm_fourierLaplace_le {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b)
    (ψ : HardySpace a b) :
    ‖fourierLaplace ψ s‖ ≤ ‖ψ‖ * ‖(evaluationVector s : HardySpace a b)‖ := by
  rw [evaluationVector_spec hs, paperInner, mul_comm]
  exact norm_inner_le_norm _ _

/-- Evaluation at an interior point is a bounded linear functional on the Fourier realization. -/
def hardyEvaluationFunctional {a b : ℝ} (s : ℂ) : HardySpace a b →L[ℂ] ℂ :=
  innerSL ℂ (evaluationVector s)

lemma hardyEvaluationFunctional_apply {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b)
    (ψ : HardySpace a b) : hardyEvaluationFunctional s ψ = fourierLaplace ψ s := by
  exact (evaluationVector_spec hs ψ).symm

lemma fourierLaplace_continuous_eval {a b : ℝ} {s : ℂ} (hs : s ∈ strip a b) :
    Continuous (fun ψ : HardySpace a b => fourierLaplace ψ s) := by
  have he : (fun ψ : HardySpace a b => fourierLaplace ψ s) =
      (hardyEvaluationFunctional s : HardySpace a b → ℂ) :=
    funext (fun ψ => (hardyEvaluationFunctional_apply hs ψ).symm)
  rw [he]
  exact (hardyEvaluationFunctional s).continuous

lemma evaluationVector_fourierLaplace_integral {a b : ℝ} {s z : ℂ}
    (hs : s ∈ strip a b) (hz : z ∈ strip a b) :
    fourierLaplace (evaluationVector z : HardySpace a b) s =
      (2 * Real.pi : ℂ)⁻¹ * ∫ τ : ℝ,
        Complex.exp ((s + conj z) * τ) / (hardyWeight a b τ : ℂ) := by
  rw [evaluationVector_eq_density hz, fourierLaplace_smul _ _ hs, fourierLaplace]
  have hc : (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ =
      (2 * Real.pi : ℂ)⁻¹ := by
    rw [← mul_inv, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  rw [← mul_assoc, hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [(volume_absolutelyContinuous_hardyMeasure a b).ae_eq
    (hardyEvaluationDensity_memLp hz).coeFn_toLp] with τ hτ
  rw [hτ]
  simp only [hardyEvaluationDensity]
  rw [div_mul_eq_mul_div, ← Complex.exp_add]
  congr 2
  ring

end ConditionalGoldbach
