import LiLiuGoldbach.Proofs.FiniteMellinProjection
import LiLiuGoldbach.Proofs.WideWeight

/-! Finite C6 model weights with arbitrary compact support strictly inside (0,1). -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

structure FiniteModelWeight (φ : ℝ → ℝ) where
  smooth : ContDiff ℝ 6 φ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_lt_one : upper < 1
  lower_le_upper : lower ≤ upper
  support_subset : Function.support φ ⊆ Icc lower upper

namespace FiniteModelWeight
lemma continuous {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) : Continuous φ := hφ.smooth.continuous
lemma hasCompactSupport {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) : HasCompactSupport φ :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc hφ.support_subset
lemma mem_support_interval {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) {u : ℝ}
    (hu : φ u ≠ 0) : u ∈ Icc hφ.lower hφ.upper := hφ.support_subset hu
lemma mem_support_unit {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) {u : ℝ}
    (hu : φ u ≠ 0) : u ∈ Ioo (0 : ℝ) 1 :=
  ⟨hφ.lower_pos.trans_le (hφ.mem_support_interval hu).1,
    (hφ.mem_support_interval hu).2.trans_lt hφ.upper_lt_one⟩
lemma eq_zero_of_nonpos {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) {u : ℝ}
    (hu : u ≤ 0) : φ u = 0 := by
  by_contra hn
  exact (not_lt_of_ge hu) (hφ.mem_support_unit hn).1
lemma norm_bounded {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) :
    ∃ B : ℝ, ∀ u : ℝ, ‖(φ u : ℂ)‖ ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := hφ.lower) (b := hφ.upper)).exists_bound_of_continuousOn
    hφ.continuous.continuousOn
  refine ⟨|B|+1,fun u => ?_⟩
  by_cases hu : φ u = 0
  · simp [hu]; positivity
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using
      (hB u (hφ.mem_support_interval hu)).trans (by linarith [le_abs_self B])
end FiniteModelWeight

namespace FiniteModel

def modelMass (φ : ℝ → ℝ) : ℝ := ∫ u in (0 : ℝ)..1, φ u * φ (1-u)

lemma companion_contDiff {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) :
    ContDiff ℝ 6 (companion φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ≠ 0
  · exact (Real.contDiffAt_sqrt hx).mul hφ.smooth.contDiffAt
  · have hx0 : x = 0 := by simpa using hx
    subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hφ.lower_pos] with u hu
    have hz : φ u = 0 := by
      by_contra hn
      exact (not_lt_of_ge (hφ.mem_support_interval hn).1) hu
    simp [companion,hz]

lemma companion_support_subset {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) :
    Function.support (companion φ) ⊆ Icc hφ.lower hφ.upper := by
  intro x hx
  exact hφ.mem_support_interval (mul_ne_zero_iff.mp hx).2

theorem mellinWeight_convergent {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) (s : ℂ) :
    MellinConvergent (fun u => (companion φ u : ℂ)) s := by
  have hsupp : Function.support (fun u : ℝ => (u : ℂ) ^ (s - 1) *
      (companion φ u : ℂ)) ⊆ Icc hφ.lower hφ.upper := by
    intro u hu
    apply companion_support_subset hφ
    intro hzero
    exact hu (by simp [hzero])
  change IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * (companion φ u : ℂ)) (Ioi 0)
  apply Integrable.integrableOn
  apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
  apply ContinuousOn.integrableOn_Icc
  intro u hu
  have hu0 : u ≠ 0 := by linarith [hu.1, hφ.lower_pos]
  exact ((Complex.continuousAt_ofReal_cpow_const u (s - 1) (Or.inr hu0)).mul
    (Complex.continuous_ofReal.continuousAt.comp (companion_contDiff hφ).continuous.continuousAt)).continuousWithinAt

lemma mellinWeight_verticalIntegrable {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ)
    (σ : ℝ) (hσ : 0 < σ) : VerticalIntegrable (mellinWeight φ) σ :=
  compact_mellin_finite_verticalIntegrable (companion φ)
    ((companion_contDiff hφ).of_le (by norm_num)) _ _ (companion_support_subset hφ) σ hσ

lemma mellinWeight_inversion {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (u : ℝ) (hu : 0 < u) :
    (companion φ u : ℂ) = verticalMellin σ (fun s => mellinWeight φ s * (u : ℂ)^(-s)) :=
  compact_mellin_finite_inversion (companion φ)
    ((companion_contDiff hφ).of_le (by norm_num)) _ _ (companion_support_subset hφ) σ hσ u hu

lemma mellinWeight_uniform_decay (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (lo hi : ℝ) (hlo : 0 < lo) (hlh : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc lo hi, ∀ t : ℝ,
      ‖mellinWeight φ (line x t)‖ ≤ C*(1+|t|)⁻¹^6 := by
  obtain ⟨C,hC,hbound⟩ := compact_mellin_finite_decay 6 (companion φ)
    (companion_contDiff hφ) _ _ (companion_support_subset hφ) lo hi hlo hlh
  refine ⟨C,hC,fun x hx t => ?_⟩
  simpa [mellinWeight,line] using hbound (line x t) (by simpa [line] using hx)

theorem mellinWeight_differentiable {φ : ℝ → ℝ} (hφ : FiniteModelWeight φ) :
    Differentiable ℂ (mellinWeight φ) := by
  have hc : Continuous (fun u : ℝ => (companion φ u : ℂ)) :=
    Complex.continuous_ofReal.comp (companion_contDiff hφ).continuous
  have htop : (fun u : ℝ => (companion φ u : ℂ)) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop hφ.upper] with u hu
    have hz : companion φ u = 0 := by
      by_contra hn
      exact (not_lt_of_ge (companion_support_subset hφ hn).2) hu
    simp [hz]
  have hbot : (fun u : ℝ => (companion φ u : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < hφ.lower from hφ.lower_pos))] with u hu
    have hz : companion φ u = 0 := by
      by_contra hn
      exact (not_lt_of_ge (companion_support_subset hφ hn).1) hu
    simp [hz]
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hc.locallyIntegrable.locallyIntegrableOn _)
  · exact htop.trans_isBigO (Asymptotics.isBigO_zero _ _)
  · linarith
  · exact hbot.trans_isBigO (Asymptotics.isBigO_zero _ _)
  · linarith

end FiniteModel
end LiLiuGoldbach16
