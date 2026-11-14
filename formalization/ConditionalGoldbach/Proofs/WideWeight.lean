module

public import ConditionalGoldbach.Proofs.CutoffSmooth
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators Topology ContDiff
open Filter Set MeasureTheory
namespace ConditionalGoldbach

lemma cutoffPolynomial_of_nonpos {t : ℝ} (ht : t≤0) : cutoffPolynomial t=0 := by simp [cutoffPolynomial,ht]
lemma cutoffPolynomial_of_one_le {t : ℝ} (ht : 1≤t) : cutoffPolynomial t=1 := by simp [cutoffPolynomial,ht,show ¬t≤0 by linarith]

lemma wideCutoff_contDiff : ContDiff ℝ 6 wideCutoff := by
  unfold wideCutoff
  exact (cutoffPolynomial_contDiff.comp (by fun_prop)).mul (cutoffPolynomial_contDiff.comp (by fun_prop))

lemma wideCutoff_reflection (x : ℝ) : wideCutoff x=wideCutoff (experimentN-x) := by
  unfold wideCutoff
  rw [show (experimentN:ℝ)-(experimentN-x)-16=x-16 by ring]
  exact mul_comm _ _

lemma wideCutoff_plateau (x : ℝ) (hx : x∈Icc (1000:ℝ) (experimentN-1000)) : wideCutoff x=1 := by
  norm_num [experimentN] at hx
  unfold wideCutoff
  rw [cutoffPolynomial_of_one_le (by norm_num; linarith [hx.1]),
    cutoffPolynomial_of_one_le (by norm_num [experimentN]; linarith [hx.2])]
  norm_num

lemma wideCutoff_zero_left (x : ℝ) (hx : x≤16) : wideCutoff x=0 := by
  unfold wideCutoff
  rw [cutoffPolynomial_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg (by linarith); norm_num)]
  simp

lemma wideCutoff_zero_right (x : ℝ) (hx : (experimentN:ℝ)-16≤x) : wideCutoff x=0 := by
  rw [wideCutoff_reflection]
  exact wideCutoff_zero_left _ (by linarith)

lemma wideCompanion_formula (u : ℝ) : wideCompanion u =
    Real.sqrt (1-u)*wideCutoff (experimentN*u)/
      Real.sqrt (Real.log (experimentN*u)*Real.log (experimentN*(1-u))) := by
  unfold wideCompanion
  split_ifs with hu
  · rfl
  · have hc : wideCutoff (experimentN*u)=0 := by
      simp only [mem_Ioo,not_and_or,not_lt] at hu
      rcases hu with hu|hu
      · apply wideCutoff_zero_left
        norm_num [experimentN] at hu ⊢
        linarith
      · apply wideCutoff_zero_right
        norm_num [experimentN] at hu ⊢
        linarith
    change (0:ℝ)=Real.sqrt (1-u)*wideCutoff ((experimentN:ℝ)*u)/Real.sqrt (Real.log ((experimentN:ℝ)*u)*Real.log ((experimentN:ℝ)*(1-u)))
    rw [hc,mul_zero,zero_div]

lemma wideCompanion_support : Function.support wideCompanion ⊆
    Ioo (16/experimentN:ℝ) (1-16/experimentN:ℝ) := by
  intro u hu
  by_contra hn
  apply hu
  unfold wideCompanion
  exact ite_eq_right hn

lemma wideWeight_support : Function.support wideWeight ⊆
    Ioo (16/experimentN:ℝ) (1-16/experimentN:ℝ) := by
  intro u hu
  apply wideCompanion_support
  intro he
  exact hu (by simp [wideWeight,he])

lemma wideWeight_hasCompactSupport : HasCompactSupport wideWeight :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (wideWeight_support.trans Ioo_subset_Icc_self)

lemma wideCompanion_hasCompactSupport : HasCompactSupport wideCompanion :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (wideCompanion_support.trans Ioo_subset_Icc_self)

lemma wideCompanion_contDiff : ContDiff ℝ 6 wideCompanion := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u∈Icc (16/experimentN:ℝ) (1-16/experimentN:ℝ)
  · have hNu : 1<(experimentN:ℝ)*u := by norm_num [experimentN] at hu ⊢; linarith [hu.1]
    have hNv : 1<(experimentN:ℝ)*(1-u) := by norm_num [experimentN] at hu ⊢; linarith [hu.2]
    have hu1 : 0<1-u := by norm_num [experimentN] at hu ⊢; linarith [hu.2]
    have he : wideCompanion = fun v => Real.sqrt (1-v)*wideCutoff (experimentN*v)/
        Real.sqrt (Real.log (experimentN*v)*Real.log (experimentN*(1-v))) := funext wideCompanion_formula
    rw [he]
    apply ContDiffAt.div
    · exact ((contDiffAt_const.sub contDiffAt_id).sqrt hu1.ne').mul
        (wideCutoff_contDiff.contDiffAt.comp u (by fun_prop))
    · apply ContDiffAt.sqrt
      · exact ((contDiffAt_const.mul contDiffAt_id).log (ne_of_gt (by linarith : 0<(experimentN:ℝ)*u))).mul
          ((contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).log
            (ne_of_gt (by linarith : 0<(experimentN:ℝ)*(1-u))))
      · exact (mul_pos (Real.log_pos hNu) (Real.log_pos hNv)).ne'
    · exact (Real.sqrt_pos.mpr (mul_pos (Real.log_pos hNu) (Real.log_pos hNv))).ne'
  · have he : wideCompanion =ᶠ[𝓝 u] fun _ => (0:ℝ) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hu] with v hv
      by_contra hs
      exact hv (Ioo_subset_Icc_self (wideCompanion_support hs))
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma wideWeight_contDiff : ContDiff ℝ 6 wideWeight := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0<u
  · unfold wideWeight
    exact wideCompanion_contDiff.contDiffAt.div (contDiffAt_id.sqrt hu.ne')
      (Real.sqrt_pos.mpr hu).ne'
  · have hupper : u < (16/experimentN:ℝ) := by
      have hh : u≤0 := le_of_not_gt hu
      norm_num [experimentN]
      linarith
    have he : wideWeight =ᶠ[𝓝 u] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hupper] with v hv
      by_contra hs
      have hh := (wideWeight_support hs).1
      change v < 16/experimentN at hv
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq he


lemma wideWeight_product (u : ℝ) (hu : u∈Ioo (16/experimentN:ℝ) (1-16/experimentN:ℝ)) :
    wideWeight u*wideWeight (1-u)=wideCutoff (experimentN*u)^2/
      (Real.log (experimentN*u)*Real.log (experimentN*(1-u))) := by
  have hu0 : 0<u := by norm_num [experimentN] at hu; linarith [hu.1]
  have hu1 : 0<1-u := by norm_num [experimentN] at hu; linarith [hu.2]
  have hNu : 1<(experimentN:ℝ)*u := by norm_num [experimentN] at hu ⊢; linarith [hu.1]
  have hNv : 1<(experimentN:ℝ)*(1-u) := by norm_num [experimentN] at hu ⊢; linarith [hu.2]
  have huS := (Real.sqrt_pos.mpr hu0).ne'
  have hvS := (Real.sqrt_pos.mpr hu1).ne'
  have hL := mul_pos (Real.log_pos hNu) (Real.log_pos hNv)
  have hLS := (Real.sqrt_pos.mpr hL).ne'
  have hsq := Real.sq_sqrt hL.le
  have hc : wideCutoff ((experimentN:ℝ)*(1-u))=wideCutoff (experimentN*u) := by
    rw [show (experimentN:ℝ)*(1-u)=experimentN-experimentN*u by ring]
    exact (wideCutoff_reflection _).symm
  simp only [wideWeight,wideCompanion_formula,sub_sub_cancel,hc]
  rw [mul_comm (Real.log (experimentN*(1-u))) (Real.log (experimentN*u))]
  field_simp;
  rw [Real.sq_sqrt (show 0 ≤ Real.log (u*(experimentN:ℝ))*Real.log ((1-u)*(experimentN:ℝ)) from by simpa only [mul_comm] using hL.le)]

lemma wideWeight_product_integrable : IntervalIntegrable (fun u : ℝ => wideWeight u*wideWeight (1-u)) volume 0 1 :=
  (wideWeight_contDiff.continuous.mul (wideWeight_contDiff.continuous.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _

lemma wideModelIntegrand_intervalIntegrable : IntervalIntegrable (fun x : ℝ => wideCutoff x^2/
    (Real.log x*Real.log ((experimentN:ℝ)-x))) volume 16 ((experimentN:ℝ)/2) := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [uIcc_of_le (by norm_num [experimentN] : (16:ℝ)≤(experimentN:ℝ)/2)] at hx
  have hx0 : 0<x := by linarith [hx.1]
  have hy0 : 0<(experimentN:ℝ)-x := by norm_num [experimentN] at hx ⊢; linarith [hx.2]
  have hx1 : 1<x := by linarith [hx.1]
  have hy1 : 1<(experimentN:ℝ)-x := by norm_num [experimentN] at hx ⊢; linarith [hx.2]
  exact ((wideCutoff_contDiff.continuous.continuousAt.pow 2).div
    ((continuousAt_id.log hx0.ne').mul ((continuousAt_const.sub continuousAt_id).log hy0.ne'))
    (mul_pos (Real.log_pos hx1) (Real.log_pos hy1)).ne').continuousWithinAt

theorem proposition_B_4_weight :
    ContDiff ℝ 6 wideWeight ∧ HasCompactSupport wideWeight ∧
    Function.support wideWeight ⊆ Ioo (0 : ℝ) 1 ∧
    IntervalIntegrable (fun u : ℝ => wideWeight u * wideWeight (1 - u)) volume 0 1 ∧
    IntervalIntegrable (fun x : ℝ => wideCutoff x ^ 2 /
      (Real.log x * Real.log ((experimentN : ℝ) - x))) volume 16 ((experimentN : ℝ) / 2)  := by
  refine ⟨wideWeight_contDiff,wideWeight_hasCompactSupport,?_,wideWeight_product_integrable,
    wideModelIntegrand_intervalIntegrable⟩
  intro u hu
  have hs := wideWeight_support hu
  norm_num [experimentN] at hs
  constructor <;> linarith [hs.1,hs.2]

end ConditionalGoldbach
