module

public import ConditionalGoldbach.Definitions.Arithmetic
public import ConditionalGoldbach.Definitions.Weights
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.UniformSpace.Uniformizable

/-! Smooth weights, positive mass, and the elementary support separation. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

theorem IsWeight.continuous {φ : ℝ → ℝ} (hφ : IsWeight φ) : Continuous φ :=
  hφ.1.continuous

theorem IsWeight.hasCompactSupport {φ : ℝ → ℝ} (hφ : IsWeight φ) :
    HasCompactSupport φ :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc hφ.2.1

theorem IsWeight.nonneg {φ : ℝ → ℝ} (hφ : IsWeight φ) (u : ℝ) : 0 ≤ φ u :=
  (hφ.2.2.1 u).1

theorem IsWeight.le_one {φ : ℝ → ℝ} (hφ : IsWeight φ) (u : ℝ) : φ u ≤ 1 :=
  (hφ.2.2.1 u).2

theorem IsWeight.mem_support_interval {φ : ℝ → ℝ} (hφ : IsWeight φ)
    {u : ℝ} (hu : φ u ≠ 0) : u ∈ Icc (1 / 3 : ℝ) (2 / 3) :=
  hφ.2.1 hu

theorem weightMass_nonneg (φ : ℝ → ℝ) : 0 ≤ weightMass φ := by
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun u => sq_nonneg (φ u))

/-- An admissible main weight is nonzero at some point. -/
lemma IsWeight.exists_ne_zero {φ : ℝ → ℝ} (hφ : IsWeight φ) : ∃ u, φ u ≠ 0 := by
  obtain ⟨_, _, _, _, hNonzero⟩ := hφ
  by_contra h
  push Not at h
  exact hNonzero (funext h)

theorem weightMass_pos {φ : ℝ → ℝ} (hφ : IsWeight φ) : 0 < weightMass φ := by
  obtain ⟨u, hu⟩ := hφ.exists_ne_zero
  have hs := hφ.mem_support_interval hu
  have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (a := (0 : ℝ)) (b := 1) (f := fun _ => (0 : ℝ)) (g := fun x => φ x ^ 2)
    (by norm_num) continuous_const.continuousOn (hφ.continuous.pow 2).continuousOn
    (fun x _ => sq_nonneg (φ x)) ⟨u, ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      sq_pos_of_ne_zero hu⟩
  simpa only [intervalIntegral.integral_zero, weightMass] using hpos

theorem theorem_1_1_weight_exists : ∃ φ : ℝ → ℝ, IsWeight φ := by
  let f : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 12, 1 / 6, by norm_num, by norm_num⟩
  refine ⟨f, f.contDiff, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [f.support_eq] at hx
    have hx' : |x - 1 / 2| < (1 / 6 : ℝ) := by
      simpa only [Metric.mem_ball, Real.dist_eq, f] using hx
    rcases abs_lt.mp hx' with ⟨hl, hr⟩
    constructor <;> linarith
  · intro x
    exact ⟨f.nonneg, f.le_one⟩
  · intro x
    have hs := f.sub (x - 1 / 2)
    convert hs.symm using 1 <;> congr 1 <;> ring
  · intro hzero
    have hone : f (1 / 2 : ℝ) = 1 :=
      f.one_of_mem_closedBall (by simp [Metric.mem_closedBall, f])
    have hz := congrFun hzero (1 / 2 : ℝ)
    simp only [Pi.zero_apply] at hz
    linarith

theorem lemma_3_5_weight_support (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (n m k : ℕ)
    (hn : φ ((n : ℝ) / N) ≠ 0) (hm : φ ((m : ℝ) / N) ≠ 0) :
    ¬positiveDifferenceFamily N n m k ∧
    ¬negativeDifferenceFamily N n m k ∧
    (sumFamily N n m k ↔ k = 1 ∧ n + m = N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hns := hφ.mem_support_interval hn
  have hms := hφ.mem_support_interval hm
  have hnlo := (le_div_iff₀ hNr).mp hns.1
  have hnhi := (div_le_iff₀ hNr).mp hns.2
  have hmlo := (le_div_iff₀ hNr).mp hms.1
  have hmhi := (div_le_iff₀ hNr).mp hms.2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hk, heq⟩
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have heqr : (m : ℝ) = n + k * N := by exact_mod_cast heq
    have hprod := mul_le_mul_of_nonneg_right hkr hNr.le
    nlinarith
  · rintro ⟨hk, heq⟩
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have heqr : (n : ℝ) = m + k * N := by exact_mod_cast heq
    have hprod := mul_le_mul_of_nonneg_right hkr hNr.le
    nlinarith
  · constructor
    · rintro ⟨hk, heq⟩
      have heqr : (n : ℝ) + m = k * N := by exact_mod_cast heq
      have hklt : k < 2 := by
        by_contra hge
        have hkr : (2 : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_not_gt hge)
        have hprod := mul_le_mul_of_nonneg_right hkr hNr.le
        nlinarith
      have hk1 : k = 1 := by omega
      exact ⟨hk1, by simpa [hk1] using heq⟩
    · rintro ⟨rfl, heq⟩
      exact ⟨by norm_num, by simpa using heq⟩

theorem weightEnergy_nonneg (φ : ℝ → ℝ) : 0 ≤ weightEnergy φ := by
  unfold weightEnergy
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le))
  exact setIntegral_nonneg measurableSet_Ioi (fun u hu => div_nonneg (sq_nonneg _) hu.le)

theorem IsWeight.eq_zero_of_nonpos {φ : ℝ → ℝ} (hφ : IsWeight φ)
    {u : ℝ} (hu : u ≤ 0) : φ u = 0 := by
  by_contra h
  have hs := hφ.mem_support_interval h
  linarith [hs.1]

theorem lemma_7_2_convolutions (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∀ y : ℝ,
      IntegrableOn (fun u : ℝ => φ u * φ (u + y)) (Ioi 0) ∧
      IntegrableOn (fun u : ℝ => φ u * φ (y - u)) (Ioi 0) ∧
      sumConvolution φ y = ∫ u in (0 : ℝ)..y, φ u * φ (y - u)) ∧
    sumConvolution φ 1 = weightMass φ ∧ IntegrableOn φ (Ioi 0) := by
  have hcompact (g : ℝ → ℝ) : HasCompactSupport (fun u => φ u * g u) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro u hu
    apply hφ.mem_support_interval
    exact (mul_ne_zero_iff.mp hu).1
  have hsum (y : ℝ) :
      sumConvolution φ y = ∫ u in (0 : ℝ)..y, φ u * φ (y - u) := by
    have hs : Function.support (fun u => φ u * φ (y - u)) ⊆ Ioc 0 y := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := mul_ne_zero_iff.mp hu
      have hs1 := hφ.mem_support_interval hu1
      have hs2 := hφ.mem_support_interval hu2
      constructor <;> linarith [hs1.1, hs2.1]
    unfold sumConvolution
    rw [intervalIntegral.integral_eq_integral_of_support_subset hs]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    simp only [mem_Ioi, not_lt] at hu
    rw [hφ.eq_zero_of_nonpos hu, zero_mul]
  refine ⟨?_, ?_, hφ.continuous.integrable_of_hasCompactSupport
    hφ.hasCompactSupport |>.integrableOn⟩
  · intro y
    refine ⟨?_, ?_, hsum y⟩
    · apply Integrable.integrableOn
      exact (hφ.continuous.mul (hφ.continuous.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport (hcompact _)
    · apply Integrable.integrableOn
      exact (hφ.continuous.mul (hφ.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport (hcompact _)
  · rw [hsum]
    unfold weightMass
    apply intervalIntegral.integral_congr
    intro u _
    change φ u * φ (1 - u) = φ u ^ 2
    rw [← hφ.2.2.2.1 u, pow_two]


theorem companion_contDiff {φ : ℝ → ℝ} (hφ : IsWeight φ) :
    ContDiff ℝ ∞ (companion φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ≠ 0
  · exact (Real.contDiffAt_sqrt hx).mul hφ.1.contDiffAt
  · have hx0 : x = 0 := by simpa using hx
    subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with u hu
    have hz : φ u = 0 := by
      by_contra hne
      exact (not_lt_of_ge (hφ.mem_support_interval hne).1) hu
    simp [companion, hz]

theorem companion_support_subset {φ : ℝ → ℝ} (hφ : IsWeight φ) :
    Function.support (companion φ) ⊆ Icc (1 / 3 : ℝ) (2 / 3) := by
  intro x hx
  exact hφ.mem_support_interval (mul_ne_zero_iff.mp hx).2

theorem derivativeWeight_continuous {φ : ℝ → ℝ} (hφ : IsWeight φ) :
    Continuous (derivativeWeight φ) := by
  exact (companion_contDiff hφ).continuous.sub
    (continuous_id.mul ((companion_contDiff hφ).continuous_deriv (by norm_num)))

theorem derivativeWeight_support_subset {φ : ℝ → ℝ} (hφ : IsWeight φ) :
    Function.support (derivativeWeight φ) ⊆ Icc (1 / 3 : ℝ) (2 / 3) := by
  have ht : tsupport (companion φ) ⊆ Icc (1 / 3 : ℝ) (2 / 3) :=
    closure_minimal (companion_support_subset hφ) isClosed_Icc
  intro x hx
  by_contra hout
  have hc : companion φ x = 0 := by
    by_contra hne
    exact hout (companion_support_subset hφ hne)
  have hd : deriv (companion φ) x = 0 := by
    by_contra hne
    exact hout (ht (support_deriv_subset hne))
  exact hx (by simp [derivativeWeight, hc, hd])

theorem proposition_7_4_norm_integrals (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (a : ℝ) :
    IntegrableOn (fun u : ℝ => derivativeWeight φ u ^ 2 / u) (Ioi 0) ∧
    IntegrableOn (fun u : ℝ =>
      Real.rpow (N * u) (2 * a) * derivativeWeight φ u ^ 2 /
        (1 + Real.rpow (N * u) (-2 * (beta - a))) / u) (Ioi 0) := by
  have hd := derivativeWeight_continuous hφ
  have hs := derivativeWeight_support_subset hφ
  have hb (u : ℝ) (hu : u ∈ Icc (1 / 3 : ℝ) (2 / 3)) : 0 < u := by
    linarith [hu.1]
  have hz (u : ℝ) (hu : u ∉ Icc (1 / 3 : ℝ) (2 / 3)) :
      derivativeWeight φ u = 0 := by
    by_contra hne
    exact hu (hs hne)
  constructor
  · have hsupport : Function.support (fun u : ℝ => derivativeWeight φ u ^ 2 / u) ⊆
        Icc (1 / 3 : ℝ) (2 / 3) := by
      intro u hu
      by_contra hnot
      exact hu (by simp [hz u hnot])
    apply Integrable.integrableOn
    apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
    apply ContinuousOn.integrableOn_Icc
    intro u hu
    exact ((hd.continuousAt.pow 2).div continuousAt_id (hb u hu).ne').continuousWithinAt
  · have hsupport : Function.support (fun u : ℝ =>
        Real.rpow (N * u) (2 * a) * derivativeWeight φ u ^ 2 /
          (1 + Real.rpow (N * u) (-2 * (beta - a))) / u) ⊆
        Icc (1 / 3 : ℝ) (2 / 3) := by
      intro u hu
      by_contra hnot
      exact hu (by simp [hz u hnot])
    apply Integrable.integrableOn
    apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
    apply ContinuousOn.integrableOn_Icc
    intro u hu
    have hu0 := hb u hu
    have hNu : (0 : ℝ) < N * u := mul_pos (by exact_mod_cast hN) hu0
    have hp (r : ℝ) : ContinuousAt (fun x : ℝ => Real.rpow (N * x) r) u :=
      (continuousAt_const.mul continuousAt_id).rpow_const (Or.inl hNu.ne')
    have hden : 1 + Real.rpow (N * u) (-2 * (beta - a)) ≠ 0 := by
      exact ne_of_gt (add_pos zero_lt_one (Real.rpow_pos_of_pos hNu _))
    exact (((hp _).mul (hd.continuousAt.pow 2)).div (continuousAt_const.add (hp _)) hden
      |>.div continuousAt_id hu0.ne').continuousWithinAt

end ConditionalGoldbach
