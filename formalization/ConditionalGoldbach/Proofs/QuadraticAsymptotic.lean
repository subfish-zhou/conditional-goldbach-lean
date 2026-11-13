import ConditionalGoldbach.Proofs.WeightNorm
import ConditionalGoldbach.Proofs.Elementary

/-! A quantitative dominated estimate for the functional norm asymptotic. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma normFunctional_pointwise_asymptotic (N : ℕ) (hlarge : Real.exp 16 < (N : ℝ))
    (u : ℝ) (hu : u ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    Real.exp 2 - Real.rpow (N * u) (2 * alpha N) /
        (1 + Real.rpow (N * u) (-2 * (beta - alpha N))) ≤
      Real.exp 2 * (30 / Real.log N) := by
  have hexp : (17 : ℝ) ≤ Real.exp 16 := by have h := Real.add_one_le_exp (16 : ℝ); norm_num at h ⊢; exact h
  have hNr : 0 < (N : ℝ) := by linarith
  have hL : 16 < Real.log N := by
    have h := Real.log_lt_log (Real.exp_pos 16) hlarge
    simpa using h
  have hLpos : 0 < Real.log N := by linarith
  have hu0 : 0 < u := by linarith [hu.1]
  have hu1 : u ≤ 1 := by linarith [hu.2]
  have hNu : 1 ≤ (N : ℝ) * u := by nlinarith [hu.1]
  have ha0 : 0 < alpha N := by unfold alpha; positivity
  have ha : alpha N ≤ 1 / 16 := by
    unfold alpha
    exact (div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 16)).2 (by linarith)
  have hNpow : Real.rpow (N : ℝ) (2 * alpha N) = Real.exp 2 := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hNr]
    congr 1
    unfold alpha
    field_simp
  have hpowprod : Real.rpow (N * u) (2 * alpha N) =
      Real.exp 2 * Real.rpow u (2 * alpha N) := by
    rw [show Real.rpow (N * u) (2 * alpha N) = Real.rpow (N : ℝ) (2 * alpha N) * Real.rpow u (2 * alpha N) from Real.mul_rpow hNr.le hu0.le, hNpow]
  have huPow0 : 0 < Real.rpow u (2 * alpha N) := Real.rpow_pos_of_pos hu0 _
  have huPow1 : Real.rpow u (2 * alpha N) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (show 0 ≤ 2 * alpha N by positivity)
  have hlogu : -3 ≤ Real.log u := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) hu.1
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0), Real.log_one] at hl
    linarith
  have huGap : 1 - Real.rpow u (2 * alpha N) ≤ 6 / Real.log N := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hu0]
    have he := Real.add_one_le_exp (Real.log u * (2 * alpha N))
    have hl : -(6 / Real.log N) ≤ Real.log u * (2 * alpha N) := by
      have h := mul_le_mul_of_nonneg_right hlogu (show 0 ≤ 2 / Real.log N by positivity)
      unfold alpha
      convert h using 1 <;> ring
    linarith
  have hsmallpow : Real.rpow u (-(1 / 8 : ℝ)) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by norm_num : (-1 : ℝ) ≤ -(1 / 8))
    rw [Real.rpow_neg_one] at h
    apply h.trans
    exact (inv_le_comm₀ hu0 (by norm_num : (0 : ℝ) < 3)).2 (by linarith [hu.1])
  have hNsmall : Real.rpow (N : ℝ) (-(1 / 8 : ℝ)) ≤ 8 / Real.log N := by
    have hp : 0 < Real.rpow (N : ℝ) (1 / 8 : ℝ) := Real.rpow_pos_of_pos hNr _
    have hLp : Real.log N ≤ 8 * Real.rpow (N : ℝ) (1 / 8 : ℝ) := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hNr]
      have h := Real.add_one_le_exp (Real.log N / 8)
      convert (show Real.log N ≤ 8 * Real.exp (Real.log N / 8) by linarith) using 1 <;> congr 1 <;> ring
    apply (le_div_iff₀ hLpos).2
    change (N : ℝ) ^ (-(1 / 8 : ℝ)) * Real.log N ≤ 8
    rw [Real.rpow_neg hNr.le, inv_mul_eq_div]
    exact (div_le_iff₀ hp).2 hLp
  let v := Real.rpow (N * u) (-2 * (beta - alpha N))
  have hv0 : 0 ≤ v := Real.rpow_nonneg (mul_nonneg hNr.le hu0.le) _
  have hv : v ≤ 24 / Real.log N := by
    calc
      v ≤ Real.rpow (N * u) (-(1 / 8 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hNu
        unfold beta
        linarith
      _ = Real.rpow (N : ℝ) (-(1 / 8 : ℝ)) * Real.rpow u (-(1 / 8 : ℝ)) :=
        Real.mul_rpow hNr.le hu0.le
      _ ≤ (8 / Real.log N) * 3 := mul_le_mul hNsmall hsmallpow (Real.rpow_nonneg hu0.le _) (by positivity)
      _ = _ := by ring
  have hratio : 1 - Real.rpow u (2 * alpha N) / (1 + v) ≤ 30 / Real.log N := by
    have hden : 0 < 1 + v := by positivity
    have heq : 1 - Real.rpow u (2 * alpha N) / (1 + v) =
        (1 - Real.rpow u (2 * alpha N) + v) / (1 + v) := by field_simp; ring
    rw [heq]
    have hnum : 0 ≤ 1 - Real.rpow u (2 * alpha N) + v := by linarith
    apply (div_le_self hnum (by linarith : 1 ≤ 1 + v)).trans
    calc
      _ ≤ 6 / Real.log N + 24 / Real.log N := add_le_add huGap hv
      _ = _ := by ring
  rw [hpowprod]
  change Real.exp 2 - Real.exp 2 * Real.rpow u (2 * alpha N) / (1 + v) ≤ _
  calc
    _ = Real.exp 2 * (1 - Real.rpow u (2 * alpha N) / (1 + v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le

lemma normFunctional_asymptotic_bound (N : ℕ) (hlarge : Real.exp 16 < (N : ℝ))
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    |normFunctional N φ (alpha N) - Real.exp 2 * weightEnergy φ| ≤
      (30 * Real.exp 2 * weightEnergy φ) / Real.log N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 16).trans hlarge
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hlarge' : Real.exp 10 < (N : ℝ) := (Real.exp_lt_exp.mpr (by norm_num)).trans hlarge
  have hlog : 0 < Real.log N := Real.log_pos ((Real.one_lt_exp_iff.mpr (by norm_num)).trans hlarge)
  rw [abs_of_nonpos (sub_nonpos.mpr (normFunctional_le_exp2_weightEnergy N hlarge' φ hφ))]
  obtain ⟨hE, hQ⟩ := proposition_7_4_norm_integrals N hNnat φ hφ (alpha N)
  have hb : (∫ u in Ioi (0 : ℝ),
      Real.exp 2 * (derivativeWeight φ u ^ 2 / u) -
        Real.rpow (N * u) (2 * alpha N) * derivativeWeight φ u ^ 2 /
          (1 + Real.rpow (N * u) (-2 * (beta - alpha N))) / u) ≤
      ∫ u in Ioi (0 : ℝ), (30 / Real.log N) * Real.exp 2 *
        (derivativeWeight φ u ^ 2 / u) := by
    apply setIntegral_mono_on ((hE.const_mul _).sub hQ) (hE.const_mul _) measurableSet_Ioi
    intro u hu
    by_cases hd : derivativeWeight φ u = 0
    · simp [hd]
    · have hs := derivativeWeight_support_subset hφ hd
      have hp := mul_le_mul_of_nonneg_right
        (normFunctional_pointwise_asymptotic N hlarge u hs)
        (div_nonneg (sq_nonneg (derivativeWeight φ u)) hu.le)
      convert hp using 1 <;> (try dsimp only [Pi.sub_apply]) <;> ring
  rw [integral_sub (hE.const_mul _) hQ, integral_const_mul, integral_const_mul] at hb
  have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2 * Real.pi)⁻¹ by positivity)
  unfold normFunctional weightEnergy
  convert h using 1 <;> ring

lemma normFunctional_asymptotic (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      |normFunctional N φ (alpha N) - Real.exp 2 * weightEnergy φ| ≤ C / Real.log N) := by
  refine ⟨30 * Real.exp 2 * weightEnergy φ + 1, ?_, ?_⟩
  · have := weightEnergy_nonneg φ
    positivity
  · obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp 16)
    refine ⟨N₀, ?_⟩
    intro N hN _
    have hlarge : Real.exp 16 < (N : ℝ) := hN₀.trans_le (by exact_mod_cast hN)
    have hlog : 0 < Real.log N := Real.log_pos ((Real.one_lt_exp_iff.mpr (by norm_num)).trans hlarge)
    exact (normFunctional_asymptotic_bound N hlarge φ hφ).trans
      (div_le_div_of_nonneg_right (by linarith) hlog.le)

end ConditionalGoldbach
