import ConditionalGoldbach.Definitions
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace ConditionalGoldbach

def positivePartPower (m : ℕ) (x : ℝ) : ℝ := (max x 0)^m

lemma positivePartPower_hasDerivAt (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    HasDerivAt (positivePartPower m) ((m:ℝ)*positivePartPower (m - 1) x) x := by
  rcases lt_trichotomy x 0 with hx|hx|hx
  · have he : positivePartPower m =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change y < 0 at hy
      simp [positivePartPower,max_eq_right hy.le,Nat.ne_of_gt (by omega : 0 < m)]
    have hd := (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
    simpa [positivePartPower,max_eq_right hx.le,Nat.ne_of_gt (by omega : 0 < m - 1)] using hd
  · subst x
    have hcont : Tendsto (positivePartPower (m - 1)) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have hc : Continuous (positivePartPower (m - 1)) := (continuous_id.max continuous_const).pow _
      simpa [positivePartPower,Nat.ne_of_gt (by omega : 0 < m - 1)] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have he : slope (positivePartPower m) 0 =ᶠ[𝓝[≠] (0:ℝ)] positivePartPower (m - 1) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy0 : y≠0 := hy
      rw [slope_fun_def_field]
      simp only [positivePartPower,max_self,zero_pow (by omega : m≠0),sub_zero]
      rcases lt_or_gt_of_ne hy0 with hy|hy
      · simp [max_eq_right hy.le,Nat.ne_of_gt (by omega : 0 < m - 1),Nat.ne_of_gt (by omega : 0 < m)]
      · rw [max_eq_left hy.le,show m = (m - 1)+1 by omega,pow_succ]
        field_simp
        simp
    have hd := hasDerivAt_iff_tendsto_slope.mpr (hcont.congr' he.symm)
    simpa [positivePartPower,Nat.ne_of_gt (by omega : 0 < m - 1)] using hd
  · have he : positivePartPower m =ᶠ[𝓝 x] fun y => y^m := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change 0 < y at hy
      simp [positivePartPower,max_eq_left hy.le]
    simpa [positivePartPower,max_eq_left hx.le] using ((hasDerivAt_id x).pow m).congr_of_eventuallyEq he

lemma positivePartPower_contDiff (k m : ℕ) (hkm : k < m) : ContDiff ℝ k (positivePartPower m) := by
  induction k generalizing m with
  | zero => exact contDiff_zero.mpr ((continuous_id.max continuous_const).pow m)
  | succ k ih =>
    have hm : 2 ≤ m := by omega
    rw [Nat.cast_add_one,contDiff_succ_iff_deriv]
    simp only [WithTop.natCast_ne_top,analyticOn_univ,IsEmpty.forall_iff,true_and]
    refine ⟨fun x => (positivePartPower_hasDerivAt m hm x).differentiableAt,?_⟩
    have he : deriv (positivePartPower m) = fun x => (m:ℝ)*positivePartPower (m - 1) x :=
      funext (fun x => (positivePartPower_hasDerivAt m hm x).deriv)
    rw [he]
    exact contDiff_const.mul (ih (m - 1) (by omega))

def cutoffPolynomialCore (t : ℝ) : ℝ :=
  1716*t^7-9009*t^8+20020*t^9-24024*t^10+16380*t^11-6006*t^12+924*t^13

lemma cutoffPolynomialCore_sum (t : ℝ) :
    (∑ j ∈ Finset.Icc 7 13, (Nat.choose 13 j:ℝ)*t^j*(1-t)^(13-j))=cutoffPolynomialCore t := by
  norm_num [Finset.sum_Icc_succ_top,Nat.choose,cutoffPolynomialCore]
  <;> ring

lemma cutoffPolynomialCore_reflection (t : ℝ) : cutoffPolynomialCore t+cutoffPolynomialCore (1-t)=1 := by
  unfold cutoffPolynomialCore
  ring

lemma cutoffPolynomial_eq_positive_parts (t : ℝ) :
    cutoffPolynomial t = cutoffPolynomialCore (max t 0)+cutoffPolynomialCore (-(max (t-1) 0)) := by
  unfold cutoffPolynomial
  split_ifs with ht ht'
  · rw [max_eq_right ht,max_eq_right (by linarith : t-1≤0)]
    norm_num [cutoffPolynomialCore]
  · rw [max_eq_left (by linarith : 0≤t),max_eq_left (by linarith : 0≤t-1)]
    convert (cutoffPolynomialCore_reflection t).symm using 1 <;> congr 1 <;> ring
  · rw [max_eq_left (by linarith : 0≤t),max_eq_right (by linarith : t-1≤0)]
    simp only [neg_zero,cutoffPolynomialCore_sum]
    norm_num [cutoffPolynomialCore]

lemma cutoffPolynomial_contDiff : ContDiff ℝ 6 cutoffPolynomial := by
  have h7 := positivePartPower_contDiff 6 7 (by norm_num)
  have h8 := positivePartPower_contDiff 6 8 (by norm_num)
  have h9 := positivePartPower_contDiff 6 9 (by norm_num)
  have h10 := positivePartPower_contDiff 6 10 (by norm_num)
  have h11 := positivePartPower_contDiff 6 11 (by norm_num)
  have h12 := positivePartPower_contDiff 6 12 (by norm_num)
  have h13 := positivePartPower_contDiff 6 13 (by norm_num)
  have hleft : ContDiff ℝ 6 (fun t => cutoffPolynomialCore (max t 0)) := by
    exact ((((((contDiff_const.mul h7).sub (contDiff_const.mul h8)).add (contDiff_const.mul h9)).sub
      (contDiff_const.mul h10)).add (contDiff_const.mul h11)).sub (contDiff_const.mul h12)).add (contDiff_const.mul h13)
  have hright : ContDiff ℝ 6 (fun t => cutoffPolynomialCore (-(max t 0))) := by
    have hh : ContDiff ℝ 6 (fun t => -1716*positivePartPower 7 t-9009*positivePartPower 8 t-
        20020*positivePartPower 9 t-24024*positivePartPower 10 t-16380*positivePartPower 11 t-
        6006*positivePartPower 12 t-924*positivePartPower 13 t) :=
      ((((((contDiff_const.mul h7).sub (contDiff_const.mul h8)).sub (contDiff_const.mul h9)).sub
        (contDiff_const.mul h10)).sub (contDiff_const.mul h11)).sub (contDiff_const.mul h12)).sub (contDiff_const.mul h13)
    convert hh using 1
    funext t
    unfold cutoffPolynomialCore positivePartPower
    ring
  have he : cutoffPolynomial = fun t => cutoffPolynomialCore (max t 0)+cutoffPolynomialCore (-(max (t-1) 0)) :=
    funext cutoffPolynomial_eq_positive_parts
  rw [he]
  exact hleft.add (hright.comp (contDiff_id.sub contDiff_const))

end ConditionalGoldbach
