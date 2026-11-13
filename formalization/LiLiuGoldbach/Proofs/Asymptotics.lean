import LiLiuGoldbach.Proofs.Elementary

set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace LiLiuGoldbach16

theorem evenEventually_of_eventually {P : ℕ → Prop} (h : ∀ᶠ N in atTop, P N) :
    EvenEventually P := by
  obtain ⟨k, hk⟩ := eventually_atTop.1 h
  exact ⟨k, fun N hN _ => hk N hN⟩

theorem tendsto_log_pow_five_div_nat :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 5 / N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := 1) (5 : ℝ)
    (by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def] using h

theorem tendsto_prime_power_error :
    Tendsto (fun N : ℕ => 4 * Real.log (N : ℝ) ^ 2 / Real.sqrt N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := 1 / 2) (2 : ℝ)
    (by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' := h.const_mul 4
  simpa [Function.comp_def, Real.sqrt_eq_rpow, mul_div_assoc] using h'

/-- A concrete admissible prescribed function, using only the positive uniform
lower bound for the singular series already proved in the existing project. -/
theorem isAdmissible_log : IsAdmissible (fun N => Real.log (N : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N _ hN
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  · intro B
    apply evenEventually_of_eventually
    exact (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop B
  · have hlim : Tendsto (fun N : ℕ =>
        (Real.log (N : ℝ) ^ 5 / N) / (2 * C2)) atTop (𝓝 0) := by
      simpa only [zero_div] using tendsto_log_pow_five_div_nat.div_const (2 * C2)
    have hevent := (tendsto_order.1 hlim).2 (1 / 4) (by norm_num)
    apply evenEventually_of_eventually
    filter_upwards [eventually_ge_atTop (1 : ℕ), hevent] with N hN hsmall
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hlower := singularSeries_uniform_lower N
    have hbase : 0 < 2 * C2 := mul_pos (by norm_num) C2_pos
    have hid : zeroFreeWidth N (fun N => Real.log (N : ℝ)) =
        (Real.log (N : ℝ) ^ 5 / N) / singularSeries N := by
      unfold zeroFreeWidth
      ring
    rw [hid]
    exact le_trans
      (div_le_div_of_nonneg_left (div_nonneg (pow_nonneg hlog 5) hNR.le) hbase hlower)
      hsmall.le

end LiLiuGoldbach16
