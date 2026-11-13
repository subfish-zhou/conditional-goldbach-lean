import ConditionalGoldbach.Proofs.BalanceBounds

set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter Set
namespace ConditionalGoldbach

lemma balanceFactor_tendsto_zero : Tendsto balanceFactor (nhdsWithin 0 (Ioi 0)) atTop := by
  have hpow : Tendsto (fun c : ℝ => (c⁻¹)^2) (nhdsWithin 0 (Ioi 0)) atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_inv_nhdsGT_zero
  apply tendsto_atTop_mono' _ ?_ hpow
  filter_upwards [self_mem_nhdsWithin] with c hc
  change 0<c at hc
  have he : 1 ≤ Real.exp (2*c) := Real.one_le_exp_iff.mpr (by positivity)
  unfold balanceFactor
  nlinarith [sq_nonneg c⁻¹, mul_nonneg (sub_nonneg.mpr he) (sq_nonneg c⁻¹)]

lemma balanceFactor_tendsto_infty : Tendsto balanceFactor atTop atTop := by
  have he : Tendsto (fun c : ℝ => Real.exp (2*c)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  apply tendsto_atTop_mono' _ ?_ he
  filter_upwards [] with c
  unfold balanceFactor
  nlinarith [mul_nonneg (Real.exp_pos (2*c)).le (sq_nonneg c⁻¹)]

end ConditionalGoldbach
