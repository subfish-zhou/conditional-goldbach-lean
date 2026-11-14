module

public import ConditionalGoldbach.Definitions.Hardy
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Weighted square-integrability on the closed Hardy strip. -/
public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma hardyWeight_pos (a b τ : ℝ) : 0 < hardyWeight a b τ := by
  unfold hardyWeight
  positivity

lemma hardyWeight_continuous (a b : ℝ) : Continuous (hardyWeight a b) := by
  unfold hardyWeight
  fun_prop

lemma volume_absolutelyContinuous_hardyMeasure (a b : ℝ) :
    (volume : Measure ℝ) ≪ hardyMeasure a b := by
  apply withDensity_absolutelyContinuous'
  · exact (hardyWeight_continuous a b).measurable.ennreal_ofReal.aemeasurable
  · exact Eventually.of_forall (fun τ => (ENNReal.ofReal_pos.mpr (hardyWeight_pos a b τ)).ne')

lemma hardySpace_aestronglyMeasurable {a b : ℝ} (ψ : HardySpace a b) :
    AEStronglyMeasurable ψ (volume : Measure ℝ) :=
  (Lp.aestronglyMeasurable ψ).mono_ac (volume_absolutelyContinuous_hardyMeasure a b)

lemma hardySpace_integrable_weighted_sq {a b : ℝ} (ψ : HardySpace a b) :
    Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * hardyWeight a b τ) := by
  have h : Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2) (hardyMeasure a b) :=
    (Lp.memLp ψ).norm.integrable_sq
  have hw := (hardyWeight_continuous a b).measurable.ennreal_ofReal
  have ht : ∀ᵐ τ : ℝ ∂volume, ENNReal.ofReal (hardyWeight a b τ) < ⊤ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  simpa [hardyMeasure, ENNReal.toReal_ofReal (hardyWeight_pos a b _).le] using
    (integrable_withDensity_iff hw ht).mp h

lemma hardy_exp_sq_le_weight {a b x : ℝ} (hx : x ∈ Icc a b) (τ : ℝ) :
    Real.exp (x * τ) ^ 2 ≤ hardyWeight a b τ := by
  rw [← Real.exp_nat_mul]
  change Real.exp (2 * (x * τ)) ≤ Real.exp (2 * a * τ) + Real.exp (2 * b * τ)
  by_cases ht : 0 ≤ τ
  · calc
      _ ≤ Real.exp (2 * b * τ) := Real.exp_le_exp.mpr (by nlinarith [hx.2])
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le
  · calc
      _ ≤ Real.exp (2 * a * τ) := Real.exp_le_exp.mpr (by nlinarith [hx.1])
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le

lemma hardy_weighted_line_memLp {a b x : ℝ} (hx : x ∈ Icc a b) (ψ : HardySpace a b) :
    MemLp (fun τ : ℝ => (Real.exp (x * τ) : ℂ) * ψ τ) 2 := by
  have hm : AEStronglyMeasurable (fun τ : ℝ => (Real.exp (x * τ) : ℂ) * ψ τ) volume :=
    (by fun_prop : Continuous (fun τ : ℝ => (Real.exp (x * τ) : ℂ))).aestronglyMeasurable.mul
      (hardySpace_aestronglyMeasurable ψ)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (hardySpace_integrable_weighted_sq ψ).mono' (hm.norm.pow 2)
  filter_upwards [] with τ
  change ‖‖(Real.exp (x * τ) : ℂ) * ψ τ‖ ^ 2‖ ≤ _
  simp only [Real.norm_eq_abs,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  simp only [abs_of_nonneg (sq_nonneg (Real.exp (x * τ))), abs_of_nonneg (sq_nonneg (‖ψ τ‖))]
  calc
    Real.exp (x * τ) ^ 2 * ‖ψ τ‖ ^ 2 ≤ hardyWeight a b τ * ‖ψ τ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hardy_exp_sq_le_weight hx τ) (sq_nonneg _)
    _ = _ := mul_comm _ _

lemma hardy_exp_memLp_Iic {c : ℝ} (hc : 0 < c) :
    MemLp (fun τ : ℝ => (Real.exp (c * τ) : ℂ)) 2 (volume.restrict (Iic 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (by fun_prop : Continuous (fun τ : ℝ => (Real.exp (c * τ) : ℂ))).aestronglyMeasurable).mpr
  have h := integrableOn_exp_mul_Iic (show 0 < 2 * c by positivity) 0
  simpa only [IntegrableOn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc] using h

lemma hardy_exp_memLp_Ioi {c : ℝ} (hc : c < 0) :
    MemLp (fun τ : ℝ => (Real.exp (c * τ) : ℂ)) 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (by fun_prop : Continuous (fun τ : ℝ => (Real.exp (c * τ) : ℂ))).aestronglyMeasurable).mpr
  have h := integrableOn_exp_mul_Ioi (show 2 * c < 0 by linarith) 0
  simpa only [IntegrableOn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc] using h

lemma hardy_exp_mul_factor (a x τ : ℝ) (z : ℂ) :
    ((Real.exp (a * τ) : ℂ) * z) * (Real.exp ((x - a) * τ) : ℂ) =
      (Real.exp (x * τ) : ℂ) * z := by
  rw [mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

lemma hardy_weighted_line_integrable {a b x : ℝ} (hx : x ∈ Ioo a b)
    (ψ : HardySpace a b) :
    Integrable (fun τ : ℝ => (Real.exp (x * τ) : ℂ) * ψ τ) := by
  have hab : a ≤ b := le_trans hx.1.le hx.2.le
  have hl := ((hardy_weighted_line_memLp (x := a) ⟨le_rfl, hab⟩ ψ).restrict (Iic 0)).integrable_mul
    (hardy_exp_memLp_Iic (show 0 < x - a by linarith [hx.1]))
  have hr := ((hardy_weighted_line_memLp (x := b) ⟨hab, le_rfl⟩ ψ).restrict (Ioi 0)).integrable_mul
    (hardy_exp_memLp_Ioi (show x - b < 0 by linarith [hx.2]))
  change Integrable (fun τ : ℝ => ((Real.exp (a * τ) : ℂ) * ψ τ) *
    (Real.exp ((x - a) * τ) : ℂ)) (volume.restrict (Iic 0)) at hl
  change Integrable (fun τ : ℝ => ((Real.exp (b * τ) : ℂ) * ψ τ) *
    (Real.exp ((x - b) * τ) : ℂ)) (volume.restrict (Ioi 0)) at hr
  simp only [hardy_exp_mul_factor] at hl hr
  have h := IntegrableOn.union hl hr
  simpa only [Iic_union_Ioi, IntegrableOn, Measure.restrict_univ] using h

lemma hardySpace_norm_sq_integral {a b : ℝ} (ψ : HardySpace a b) :
    ‖ψ‖ ^ 2 = ∫ τ : ℝ, ‖ψ τ‖ ^ 2 * hardyWeight a b τ := by
  have h : ‖ψ‖ ^ 2 = ∫ τ : ℝ, ‖ψ τ‖ ^ 2 ∂hardyMeasure a b := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [h]
  change (∫ τ : ℝ, ‖ψ τ‖ ^ 2 ∂(volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ)))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (hardyWeight_continuous a b).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hardyWeight_pos a b _).le, smul_eq_mul, mul_comm]

end ConditionalGoldbach
