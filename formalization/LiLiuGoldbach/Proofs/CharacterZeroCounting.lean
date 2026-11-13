import LiLiuGoldbach.Proofs.CharacterZerosCompact
import LiLiuGoldbach.Proofs.CharacterGrowthFoundation
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Data.Set.Card.Arithmetic

/-! Jensen bounds with the same multiplicity index as the paper. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter MeromorphicOn
namespace LiLiuGoldbach16

lemma divisor_eq_orderNat {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K)
    {z : ℂ} (hz : z ∈ K) : divisor f K z = (analyticOrderNatAt f z : ℤ) := by
  rw [hf.divisor_apply hz]
  by_cases h : analyticOrderAt f z = ⊤
  · simp [analyticOrderNatAt, h]
  · rw [← Nat.cast_analyticOrderNatAt h]
    simp

lemma zeroIndex_ncard_le_divisor_sum {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    (S : Set (ZeroIndex χ)) (c : ℂ) (r : ℝ)
    (hS : ∀ p ∈ S, p.val.1 ∈ closedBall c r) :
    (S.ncard : ℝ) ≤ ∑ᶠ z, (divisor χ.LFunction (closedBall c r) z : ℝ) := by
  classical
  let K : Set ℂ := closedBall c r ∩ χ.LFunction ⁻¹' {0}
  have hK : K.Finite := LFunction_zeros_compact_finite χ hχ (isCompact_closedBall ..)
  let B : Set (ℂ × ℕ) := ⋃ z ∈ K, ({z} : Set ℂ) ×ˢ Iio (analyticOrderNatAt χ.LFunction z)
  have hB : B.Finite := hK.biUnion (fun z _ => (finite_singleton z).prod (Set.finite_Iio _))
  have hcard : S.ncard ≤ B.ncard := by
    apply Set.ncard_le_ncard_of_injOn Subtype.val _ Subtype.val_injective.injOn hB
    intro p hp
    simp only [B, mem_iUnion, mem_prod, mem_singleton_iff, mem_Iio]
    exact ⟨p.val.1, ⟨hS p hp, p.property.2.2.1⟩, rfl, p.property.2.2.2⟩
  have hcardB : B.ncard ≤ ∑ z ∈ hK.toFinset, analyticOrderNatAt χ.LFunction z := by
    have hb := hK.ncard_biUnion_le (fun z => ({z} : Set ℂ) ×ˢ Iio (analyticOrderNatAt χ.LFunction z))
    simpa only [ncard_prod, ncard_singleton, Set.ncard_Iio_nat, one_mul,
      finsum_mem_eq_finite_toFinset_sum _ hK] using hb
  have ha : AnalyticOnNhd ℂ χ.LFunction (closedBall c r) := fun z _ =>
    (χ.differentiable_LFunction hχ).analyticAt z
  have heq : (∑ z ∈ hK.toFinset, (analyticOrderNatAt χ.LFunction z : ℝ)) =
      ∑ᶠ z, (divisor χ.LFunction (closedBall c r) z : ℝ) := by
    rw [finsum_eq_sum_of_support_subset]
    · apply Finset.sum_congr rfl
      intro z hz
      rw [divisor_eq_orderNat ha (hK.mem_toFinset.mp hz).1]
      norm_cast
    · intro z hz
      simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hz
      have hzB := (divisor χ.LFunction (closedBall c r)).supportWithinDomain hz
      have hz0 : χ.LFunction z = 0 := by
        by_contra hne
        have hh := ((χ.differentiable_LFunction hχ).analyticAt z).analyticOrderAt_eq_zero.mpr hne
        have hd := divisor_eq_orderNat ha hzB
        simp only [analyticOrderNatAt, hh, ENat.toNat_zero, Int.natCast_zero] at hd
        exact hz hd
      exact hK.mem_toFinset.mpr ⟨hzB,hz0⟩
  rw [← heq, ← Nat.cast_sum]
  exact_mod_cast hcard.trans hcardB

lemma LFunction_zero_count_right_half_closed {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    (t : ℝ) :
    (({p : ZeroIndex χ | 1/2 ≤ p.val.1.re ∧ t ≤ p.val.1.im ∧ p.val.1.im ≤ t+1} : Set _).ncard : ℝ)
      ≤ Real.log (26*(d : ℝ)*(|t|+2)) / Real.log ((11/4 : ℝ)/(8/3)) := by
  let c : ℂ := 3 + ((t+1/2 : ℝ) : ℂ)*I
  let S : Set (ZeroIndex χ) := {p | 1/2 ≤ p.val.1.re ∧ t ≤ p.val.1.im ∧ p.val.1.im ≤ t+1}
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hcre : c.re = 3 := by simp [c]
  have hcim : c.im = t+1/2 := by simp [c]
  have hcnorm : ‖c‖ ≤ 7/2+|t| := by
    calc
      _ ≤ |c.re|+|c.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = 3+|t+1/2| := by rw [hcre,hcim]; norm_num
      _ ≤ _ := by have hh := abs_add_le t (1/2 : ℝ); norm_num at hh; linarith
  have ha : AnalyticOnNhd ℂ χ.LFunction (closedBall c |(11/4 : ℝ)|) := fun z _ =>
    (χ.differentiable_LFunction hχ).analyticAt z
  have hlower : (1/2 : ℝ) ≤ ‖χ.LFunction c‖ := LFunction_right_lower_bound χ c hcre.ge
  have hbound (z : ℂ) (hz : z ∈ sphere c |(11/4 : ℝ)|) :
      ‖χ.LFunction z‖ ≤ 13*(d : ℝ)*(|t|+2) := by
    have hzdist : ‖z-c‖ = 11/4 := by simpa only [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ)<11/4)] using hz
    have hzre : 1/4 ≤ z.re := by
      have hh := (neg_le_abs (z-c).re).trans (Complex.abs_re_le_norm (z-c))
      simp only [sub_re,hcre,hzdist] at hh
      linarith
    have hpoly := LFunction_polynomial_bound χ hχ z (by linarith)
    have hdiv : ‖z‖/z.re ≤ 4*‖z‖ := by
      have hh := div_le_div_of_nonneg_left (norm_nonneg z) (by norm_num : (0 : ℝ)<1/4) hzre
      convert hh using 1 <;> ring
    have hnorm := norm_add_le (z-c) c
    rw [sub_add_cancel, hzdist] at hnorm
    apply hpoly.trans
    have hn : 1+‖z‖/z.re ≤ 13*(|t|+2) := by linarith [abs_nonneg t]
    convert mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ)≤d) using 1 <;> ring
  have hzero : χ.LFunction c ≠ 0 := by intro he; rw [he,norm_zero] at hlower; norm_num at hlower
  have hJ := ha.sum_divisor_le (r := 8/3) (R := 11/4) (M := 13*(d : ℝ)*(|t|+2))
    (by norm_num) (by norm_num) (by nlinarith [abs_nonneg t]) hzero hbound
  have hS : ∀ p ∈ S, p.val.1 ∈ closedBall c (8/3) := by
    intro p hp
    have hre : |(p.val.1-c).re| ≤ 5/2 := by
      apply abs_le.mpr
      simp only [sub_re,hcre]
      exact ⟨by linarith [hp.1], by linarith [p.property.2.1]⟩
    have him : |(p.val.1-c).im| ≤ 1/2 := by
      apply abs_le.mpr
      simp only [sub_im,hcim]
      exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hre2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 5/2)).mpr hre
    have him2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/2)).mpr him
    simp only [sq_abs] at hre2 him2
    rw [mem_closedBall, dist_eq_norm]
    have hsq : ‖p.val.1-c‖^2 = (p.val.1-c).re^2+(p.val.1-c).im^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (p.val.1-c)]
  apply (zeroIndex_ncard_le_divisor_sum χ hχ S c (8/3) hS).trans
  have hJ' : (∑ᶠ z, (divisor χ.LFunction (closedBall c (8/3)) z : ℝ)) ≤
      Real.log (13*(d : ℝ)*(|t|+2)/‖χ.LFunction c‖) / Real.log ((11/4 : ℝ)/(8/3)) := by
    convert hJ using 1
    · rw [abs_of_pos (by norm_num : (0 : ℝ) < 8/3)]
      simpa using (map_finsum (Int.castRingHom ℝ)
        ((divisor χ.LFunction (closedBall c (8/3))).finiteSupport (isCompact_closedBall ..))).symm
  apply hJ'.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  apply Real.log_le_log (by positivity)
  apply (div_le_iff₀ (by linarith : 0 < ‖χ.LFunction c‖)).mpr
  nlinarith [mul_nonneg (show 0 ≤ (d : ℝ)*(|t|+2) by positivity) (sub_nonneg.mpr hlower)]

end LiLiuGoldbach16
