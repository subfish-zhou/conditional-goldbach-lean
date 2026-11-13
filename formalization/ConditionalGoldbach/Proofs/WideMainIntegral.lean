import ConditionalGoldbach.Proofs.WidePrimePowerCount

/-! Symmetry and scaling of the full wide-weight main integral. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set
namespace ConditionalGoldbach

lemma wideModelMass_half : wideModelMass =
    2 * ∫ u in (16/experimentN : ℝ)..(1/2 : ℝ), wideWeight u*wideWeight (1-u) := by
  let F := fun u : ℝ => wideWeight u*wideWeight (1-u)
  have hc : Continuous F := wideWeight_contDiff.continuous.mul
    (wideWeight_contDiff.continuous.comp (continuous_const.sub continuous_id))
  have href : (∫ u in (1/2 : ℝ)..1, F u) = ∫ u in (0 : ℝ)..(1/2 : ℝ), F u := by
    have hh := intervalIntegral.integral_comp_sub_left F (a := (0 : ℝ)) (b := (1/2 : ℝ)) 1
    simpa only [F,sub_sub_cancel,mul_comm,sub_zero,show (1 : ℝ)-1/2=1/2 by norm_num] using hh.symm
  have hzero : (∫ u in (0 : ℝ)..(16/experimentN : ℝ), F u) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with u
    intro hu
    rw [uIoc_of_le (by norm_num [experimentN])] at hu
    have hw : wideWeight u = 0 := by
      by_contra hh
      have h := (wideWeight_support hh).1
      linarith [hu.2]
    simp [F,hw]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (1/2)) (hc.intervalIntegrable (μ := volume) (1/2) 1)
  have hsmall := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 (16/experimentN)) (hc.intervalIntegrable (μ := volume) (16/experimentN) (1/2))
  change (∫ u in (0 : ℝ)..1, F u) = _
  rw [href] at hsplit
  rw [hzero,zero_add] at hsmall
  rw [← hsplit,← hsmall]
  ring

lemma wideModelMass_scaled : (experimentN : ℝ)*wideModelMass/2 =
    ∫ x in (16 : ℝ)..((experimentN : ℝ)/2),
      wideCutoff x^2/(Real.log x*Real.log ((experimentN : ℝ)-x)) := by
  rw [wideModelMass_half]
  let G := fun x : ℝ => wideCutoff x^2/(Real.log x*Real.log ((experimentN : ℝ)-x))
  have he : (∫ u in (16/experimentN : ℝ)..(1/2 : ℝ), wideWeight u*wideWeight (1-u)) =
      ∫ u in (16/experimentN : ℝ)..(1/2 : ℝ), G ((experimentN : ℝ)*u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u
    intro hu
    rw [uIoc_of_le (by norm_num [experimentN])] at hu
    have hu' : u ∈ Ioo (16/experimentN : ℝ) (1-16/experimentN : ℝ) := by
      constructor
      · exact hu.1
      · norm_num [experimentN] at hu ⊢
        linarith [hu.2]
    rw [wideWeight_product u hu']
    dsimp [G]
    congr 3
    ring
  rw [he,intervalIntegral.integral_comp_mul_left G (by norm_num [experimentN] : (experimentN : ℝ) ≠ 0)]
  norm_num [experimentN,smul_eq_mul]
  dsimp [G]
  ring

theorem lemma_B_3_main_integral :
    wideMainIntegral = (experimentN : ℝ) * singularSeries experimentN * wideModelMass / 2 ∧
    (unorderedPrimePairs : ℝ) = wideMainIntegral - (experimentN : ℝ) / 2 * wideResidual -
      primePowerCorrection / 2 + edgeCorrection := by
  have hm : wideMainIntegral = (experimentN : ℝ) * singularSeries experimentN * wideModelMass / 2 := by
    unfold wideMainIntegral
    rw [← wideModelMass_scaled]
    ring
  refine ⟨hm, ?_⟩
  rw [proposition_B_1.2.2.2.2,hm]
  unfold wideResidual
  ring

end ConditionalGoldbach
