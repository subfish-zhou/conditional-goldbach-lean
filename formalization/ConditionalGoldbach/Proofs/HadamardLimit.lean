import ConditionalGoldbach.Proofs.HadamardApproximation
import ConditionalGoldbach.Proofs.CharacterZeroMultiplicity
import ConditionalGoldbach.Proofs.SpectralCompletedLGrowth

/-! The full Hadamard difference identity, as the limit of actual finite zero factorizations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter MeromorphicOn
namespace ConditionalGoldbach

lemma log_scaled_radius_div_tendsto :
    Tendsto (fun R : ℝ => Real.log (8*R+2)/R) atTop (𝓝 0) := by
  have hlin : Tendsto (fun R : ℝ => 8*R+2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop ((b-2)/8)] with R hR
    linarith
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1/8) (-1/4) 1 (by norm_num)).comp hlin
  convert hh using 1
  funext R
  simp only [Function.comp_def,pow_one]
  congr 1
  ring

lemma hadamard_error_tendsto (A B d : ℝ) :
    Tendsto (fun R : ℝ => (4*(A*(8*R)*Real.log (8*R+2)+B)/R^2)*d) atTop (𝓝 0) := by
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hh := ((log_scaled_radius_div_tendsto.const_mul (32*A)).add
    ((hi.pow 2).const_mul (4*B))).mul_const d
  simp only [mul_zero,zero_pow (by decide : (2 : ℕ)≠0),zero_add,zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  field_simp
  ring

lemma zeroIndex_disk_exhaustion {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1) :
    Tendsto (fun R : ℝ => (zeroIndex_preimage_compact_finite χ hχ
      (isCompact_closedBall (0 : ℂ) (4*R))).toFinset) atTop atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro S
  let B : ℝ := 1+∑ p ∈ S, ‖p.val.1‖
  have hB : 0 < B := by dsimp [B]; positivity
  filter_upwards [eventually_ge_atTop B] with R hR
  intro p hp
  apply (zeroIndex_preimage_compact_finite χ hχ (isCompact_closedBall (0 : ℂ) (4*R))).mem_toFinset.mpr
  apply mem_closedBall_zero_iff.mpr
  have hh : ‖p.val.1‖ ≤ ∑ q ∈ S, ‖q.val.1‖ := Finset.single_le_sum (f := fun q : ZeroIndex χ => ‖q.val.1‖) (fun q _ => norm_nonneg q.val.1) hp
  dsimp [B] at hR hB
  linarith

lemma completedL_logDerivative_difference {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (u v : ℂ)
    (hu : completedL χ u ≠ 0) (hv : completedL χ v ≠ 0) :
    deriv (completedL χ) u/completedL χ u - deriv (completedL χ) v/completedL χ v =
      zeroDifference χ u v := by
  let f := completedL χ
  have hf : Differentiable ℂ f := completedL_differentiable χ hχ
  have hf0 : f 0 ≠ 0 := completedL_zero_ne_zero χ hχ hprim
  let F : ZeroIndex χ → ℂ := fun p => 1/(u-p.val.1)-1/(v-p.val.1)
  let S : ℝ → Finset (ZeroIndex χ) := fun R =>
    (zeroIndex_preimage_compact_finite χ hχ (isCompact_closedBall (0 : ℂ) (4*R))).toFinset
  have hsum : Tendsto (fun R : ℝ => ∑ p ∈ S R, F p) atTop (𝓝 (zeroDifference χ u v)) := by
    have hh := (primitive_zero_difference_summable_norm χ hχ hprim u v hu hv).of_norm.hasSum
    exact hh.comp (zeroIndex_disk_exhaustion χ hχ)
  obtain ⟨A,hA,hgrowth⟩ := completedL_disk_growth χ hχ hprim
  let B : ℝ := ‖f 0‖+1-Real.log ‖f 0‖
  have hlim := hadamard_error_tendsto A B ‖u-v‖
  have happrox : ∀ᶠ R : ℝ in atTop,
      ‖(∑ p ∈ S R, F p)-(logDeriv f u-logDeriv f v)‖ ≤
        (4*(A*(8*R)*Real.log (8*R+2)+B)/R^2)*‖u-v‖ := by
    filter_upwards [eventually_gt_atTop (max 1 (max ‖u‖ ‖v‖))] with R hR
    have hR1 : 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
    have hRp : 0 < R := by linarith
    let E : ℝ := A*(8*R)*Real.log (8*R+2)+‖f 0‖+1
    let M : ℝ := Real.exp E
    have hE : ‖f 0‖ < E := by
      have hl : 0 < Real.log (8*R+2) := Real.log_pos (by linarith)
      dsimp [E]
      nlinarith [mul_pos (mul_pos hA (by linarith : 0 < 8*R)) hl]
    have hM : ‖f 0‖ < M := by
      have hh := Real.add_one_le_exp E
      dsimp [M]
      linarith
    have hbound : ∀ z ∈ sphere (0 : ℂ) (8*R), ‖f z‖ ≤ M := by
      intro z hz
      apply (hgrowth (8*R) (by linarith) z (mem_sphere_zero_iff_norm.mp hz).le).trans
      apply Real.exp_le_exp.mpr
      dsimp [E]
      linarith [norm_nonneg (f 0)]
    have hh := logarithmicDerivative_disk_approximation f hf hf0 R M hRp hM hbound u v
      (mem_ball_zero_iff.mpr ((le_max_left ‖u‖ ‖v‖).trans (le_max_right 1 _)|>.trans_lt hR))
      (mem_ball_zero_iff.mpr ((le_max_right ‖u‖ ‖v‖).trans (le_max_right 1 _)|>.trans_lt hR)) hu hv
    dsimp only at hh
    rw [completed_divisor_sum_eq_zeroIndex_sum χ hχ hprim (4*R)
      (fun z => 1/(u-z)-1/(v-z))] at hh
    have hlog : Real.log (M/‖f 0‖) = A*(8*R)*Real.log (8*R+2)+B := by
      rw [Real.log_div (Real.exp_ne_zero E) (norm_ne_zero_iff.mpr hf0),Real.log_exp]
      dsimp [E,B]
      ring
    rw [hlog,norm_sub_rev] at hh
    exact hh
  have hlimsum : Tendsto (fun R : ℝ => ∑ p ∈ S R, F p) atTop
      (𝓝 (logDeriv f u-logDeriv f v)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) happrox hlim
  exact (tendsto_nhds_unique hlimsum hsum)

theorem lemma_3_3 : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ (_ : NeZero d), ∀ χ : Character d,
    χ.IsPrimitive → χ (-1) = -1 →
    (∀ u u₀ : ℂ, completedL χ u ≠ 0 → completedL χ u₀ ≠ 0 →
      deriv (completedL χ) u / completedL χ u -
        deriv (completedL χ) u₀ / completedL χ u₀ = zeroDifference χ u u₀) ∧
    NormallySummableOn (fun p : ZeroIndex χ => fun u : ℂ × ℂ =>
      1 / (u.1 - p.val.1) - 1 / (u.2 - p.val.1))
      {u | completedL χ u.1 ≠ 0 ∧ completedL χ u.2 ≠ 0} ∧
    (∀ t, (zeroWindow χ t).Finite ∧
      ((zeroWindow χ t).ncard : ℝ) ≤ C * Real.log (d * (|t| + 2))) := by
  obtain ⟨C,hC,hcount⟩ := primitive_local_zero_count
  refine ⟨C,hC,fun d _ χ hprim hodd => ?_⟩
  have hχ := odd_character_ne_one χ hodd
  exact ⟨completedL_logDerivative_difference χ hχ hprim,
    primitive_zero_difference_normallySummable χ hχ hprim,
    hcount d inferInstance χ hχ hprim⟩

end ConditionalGoldbach
