import LiLiuGoldbach.Proofs.FiniteModelBasic

/-! C6 convolution densities with general positive compact support and nonsymmetric mass. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff Convolution
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16.FiniteModel

theorem lemma_7_2_convolutions (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    (∀ y : ℝ,
      IntegrableOn (fun u : ℝ => φ u * φ (u + y)) (Ioi 0) ∧
      IntegrableOn (fun u : ℝ => φ u * φ (y - u)) (Ioi 0) ∧
      sumConvolution φ y = ∫ u in (0 : ℝ)..y, φ u * φ (y - u)) ∧
    sumConvolution φ 1 = modelMass φ ∧ IntegrableOn φ (Ioi 0) := by
  have hlo := hφ.lower_pos
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
    rfl


lemma differenceConvolution_support (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    Function.support (differenceConvolution φ) ⊆ Icc (hφ.lower-hφ.upper) (hφ.upper-hφ.lower) := by
  intro y hy
  by_contra h
  apply hy
  unfold differenceConvolution
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  by_contra hn
  obtain ⟨hu, huy⟩ := mul_ne_zero_iff.mp hn
  have h₁ := hφ.mem_support_interval hu
  have h₂ := hφ.mem_support_interval huy
  apply h
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

lemma sumConvolution_support (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    Function.support (sumConvolution φ) ⊆ Icc (2*hφ.lower) (2*hφ.upper) := by
  intro y hy
  by_contra h
  apply hy
  unfold sumConvolution
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  by_contra hn
  obtain ⟨hu, huy⟩ := mul_ne_zero_iff.mp hn
  have h₁ := hφ.mem_support_interval hu
  have h₂ := hφ.mem_support_interval huy
  apply h
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

lemma differenceConvolution_eq_real_integral (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (y : ℝ) :
    differenceConvolution φ y = ∫ u : ℝ, φ u * φ (u + y) := by
  unfold differenceConvolution
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  rw [hφ.eq_zero_of_nonpos (by simpa only [mem_Ioi, not_lt] using hu), zero_mul]

lemma sumConvolution_eq_convolution (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    sumConvolution φ = φ ⋆ φ := by
  funext y
  unfold sumConvolution convolution
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  rw [hφ.eq_zero_of_nonpos (by simpa only [mem_Ioi, not_lt] using hu), zero_mul]

lemma differenceConvolution_eq_convolution (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (y : ℝ) :
    differenceConvolution φ y = (φ ⋆ (fun u => φ (-u))) (-y) := by
  rw [differenceConvolution_eq_real_integral φ hφ]
  unfold convolution
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  congr 2
  ring

lemma sumConvolution_contDiff (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    ContDiff ℝ 6 (sumConvolution φ) := by
  rw [sumConvolution_eq_convolution φ hφ]
  exact hφ.hasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hφ.continuous.locallyIntegrable hφ.smooth

lemma differenceConvolution_contDiff (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    ContDiff ℝ 6 (differenceConvolution φ) := by
  have heq : differenceConvolution φ = fun y => (φ ⋆ (fun u => φ (-u))) (-y) :=
    funext (differenceConvolution_eq_convolution φ hφ)
  rw [heq]
  have hc : HasCompactSupport (fun u : ℝ => φ (-u)) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -hφ.upper) (b := -hφ.lower))
    intro u hu
    have hs := hφ.mem_support_interval hu
    constructor <;> linarith [hs.1, hs.2]
  exact (hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hφ.continuous.locallyIntegrable (hφ.smooth.comp contDiff_neg)).comp contDiff_neg

lemma differenceConvolution_even (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (y : ℝ) :
    differenceConvolution φ (-y) = differenceConvolution φ y := by
  rw [differenceConvolution_eq_real_integral φ hφ, differenceConvolution_eq_real_integral φ hφ]
  rw [← integral_add_right_eq_self (fun u : ℝ => φ u * φ (u + -y)) y]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [add_neg_cancel_right]
  ring

lemma convolution_integer_values (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    (∀ k : ℕ, 1 ≤ k → differenceConvolution φ k = 0) ∧
    (∀ k : ℕ, 2 ≤ k → sumConvolution φ k = 0) ∧
    signedConvolution φ 1 = -modelMass φ := by
  have hlo := hφ.lower_pos
  have hhi := hφ.upper_lt_one
  have hC : ∀ k : ℕ, 1 ≤ k → differenceConvolution φ k = 0 := by
    intro k hk
    by_contra hn
    have hh := differenceConvolution_support φ hφ hn
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [hh.2]
  refine ⟨hC, ?_, ?_⟩
  · intro k hk
    by_contra hn
    have hh := sumConvolution_support φ hφ hn
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [hh.2]
  · unfold signedConvolution
    rw [show differenceConvolution φ 1 = 0 from by simpa using hC 1 le_rfl,
      (lemma_7_2_convolutions φ hφ).2.1]
    ring

lemma differenceConvolution_integral (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    (∫ y in Ioi (0 : ℝ), differenceConvolution φ y) =
      (∫ u in Ioi (0 : ℝ), φ u) ^ 2 / 2 := by
  have hi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφ.hasCompactSupport
  have hφint : (∫ u in Ioi (0 : ℝ), φ u) = ∫ u : ℝ, φ u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    exact hφ.eq_zero_of_nonpos (by simpa only [mem_Ioi, not_lt] using hu)
  have hCabs : (fun y : ℝ => differenceConvolution φ |y|) = differenceConvolution φ := by
    funext y
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg (lt_of_not_ge hy), differenceConvolution_even φ hφ]
  have htotal : (∫ y : ℝ, differenceConvolution φ y) = (∫ u : ℝ, φ u) ^ 2 := by
    simp_rw [differenceConvolution_eq_convolution φ hφ]
    rw [integral_neg_eq_self, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hi hi.comp_neg,
      integral_neg_eq_self]
    simp [pow_two]
  have habs := integral_comp_abs (f := differenceConvolution φ)
  rw [hCabs, htotal] at habs
  rw [hφint]
  linarith

lemma sumConvolution_integral (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    (∫ y in Ioi (0 : ℝ), sumConvolution φ y) = (∫ u in Ioi (0 : ℝ), φ u) ^ 2 := by
  have hi := (lemma_7_2_convolutions φ hφ).2.2
  simp_rw [fun y => ((lemma_7_2_convolutions φ hφ).1 y).2.2]
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, pow_two] using
    integral_posConvolution hi hi (ContinuousLinearMap.lsmul ℝ ℝ)

lemma signedConvolution_contDiff (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    ContDiff ℝ 6 (signedConvolution φ) := by
  unfold signedConvolution
  exact (contDiff_const.mul (differenceConvolution_contDiff φ hφ)).sub (sumConvolution_contDiff φ hφ)

lemma signedConvolution_support (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    Function.support (signedConvolution φ) ⊆ Icc (hφ.lower-hφ.upper) (2*hφ.upper) := by
  have hlo := hφ.lower_pos
  have hlu := hφ.lower_le_upper
  intro y hy
  by_cases hc : differenceConvolution φ y = 0
  · have hj : sumConvolution φ y ≠ 0 := by
      intro hj
      apply hy
      simp [signedConvolution, hc, hj]
    have hs := sumConvolution_support φ hφ hj
    constructor <;> linarith [hs.1, hs.2]
  · have hs := differenceConvolution_support φ hφ hc
    constructor <;> linarith [hs.1, hs.2]

lemma signedConvolution_hasCompactSupport (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    HasCompactSupport (signedConvolution φ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (signedConvolution_support φ hφ)

lemma signedConvolution_integral_zero (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    (∫ y in Ioi (0 : ℝ), signedConvolution φ y) = 0 := by
  have hC : Integrable (differenceConvolution φ) :=
    (differenceConvolution_contDiff φ hφ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (differenceConvolution_support φ hφ))
  have hJ : Integrable (sumConvolution φ) :=
    (sumConvolution_contDiff φ hφ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (sumConvolution_support φ hφ))
  unfold signedConvolution
  rw [integral_sub ((hC.const_mul 2).integrableOn) hJ.integrableOn, integral_const_mul,
    differenceConvolution_integral φ hφ, sumConvolution_integral φ hφ]
  ring

lemma signedConvolution_mellin_one (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) :
    mellin (fun y => (signedConvolution φ y : ℂ)) 1 = 0 := by
  unfold mellin
  simp only [sub_self, cpow_zero, one_smul]
  have h := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := signedConvolution φ)
  rw [signedConvolution_integral_zero φ hφ] at h
  simpa using h

lemma signedConvolution_mellin_regular (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun y => (signedConvolution φ y : ℂ)) s ∧
    DifferentiableAt ℂ (mellin (fun y => (signedConvolution φ y : ℂ))) s := by
  have hc : Continuous (fun y => (signedConvolution φ y : ℂ)) :=
    Complex.continuous_ofReal.comp (signedConvolution_contDiff φ hφ).continuous
  have htop : (fun y => (signedConvolution φ y : ℂ)) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (2*hφ.upper)] with y hy
    have hz : signedConvolution φ y = 0 := by
      by_contra hn
      exact (not_lt_of_ge (signedConvolution_support φ hφ hn).2) hy
    simp [hz]
  have hbot : (fun y => (signedConvolution φ y : ℂ)) =O[𝓝[>] (0 : ℝ)]
      (fun y : ℝ => y ^ (-(0 : ℝ))) := by
    simpa using (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have hloc := (hc.locallyIntegrable (μ := volume)).locallyIntegrableOn (Ioi (0 : ℝ))
  exact ⟨mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0) hloc
      (htop.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith) hbot hs,
    mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hloc
      (htop.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith) hbot hs⟩

end LiLiuGoldbach16.FiniteModel
