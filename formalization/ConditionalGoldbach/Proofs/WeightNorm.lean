module

public import ConditionalGoldbach.Proofs.Weights

/-! The uniform weight-functional bound, proved from its integral formula. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

theorem normFunctional_le_exp2_weightEnergy (N : ℕ)
    (hlarge : Real.exp 10 < (N : ℝ)) (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    normFunctional N φ (alpha N) ≤ Real.exp 2 * weightEnergy φ := by
  have hexp : (1 : ℝ) < Real.exp 10 := by
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hN1 : (1 : ℝ) < N := hexp.trans hlarge
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have ha : 0 ≤ 2 * alpha N := by
    unfold alpha
    positivity
  have hNpow : Real.rpow (N : ℝ) (2 * alpha N) = Real.exp 2 := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hNpos]
    congr 1
    unfold alpha
    field_simp
  obtain ⟨hE, hQ⟩ := proposition_7_4_norm_integrals N hNnat φ hφ (alpha N)
  have hbound : (∫ u in Ioi (0 : ℝ),
      Real.rpow (N * u) (2 * alpha N) * derivativeWeight φ u ^ 2 /
        (1 + Real.rpow (N * u) (-2 * (beta - alpha N))) / u) ≤
      ∫ u in Ioi (0 : ℝ), Real.exp 2 * (derivativeWeight φ u ^ 2 / u) := by
    apply setIntegral_mono_on hQ (hE.const_mul _) measurableSet_Ioi
    intro u hu
    by_cases hd : derivativeWeight φ u = 0
    · simp [hd]
    · have hs := derivativeWeight_support_subset hφ hd
      have hule : u ≤ 1 := by linarith [hs.2]
      have hNu0 : 0 ≤ (N : ℝ) * u := mul_nonneg hNpos.le hu.le
      have hNule : (N : ℝ) * u ≤ N := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hule hNpos.le
      have hp : Real.rpow (N * u) (2 * alpha N) ≤ Real.exp 2 := by
        rw [← hNpow]
        exact Real.rpow_le_rpow hNu0 hNule ha
      have hden : 1 ≤ 1 + Real.rpow (N * u) (-2 * (beta - alpha N)) := by
        exact le_add_of_nonneg_right (Real.rpow_nonneg hNu0 _)
      have hnum : 0 ≤ Real.rpow (N * u) (2 * alpha N) * derivativeWeight φ u ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hNu0 _) (sq_nonneg _)
      calc
        Real.rpow (N * u) (2 * alpha N) * derivativeWeight φ u ^ 2 /
            (1 + Real.rpow (N * u) (-2 * (beta - alpha N))) / u
            ≤ (Real.rpow (N * u) (2 * alpha N) * derivativeWeight φ u ^ 2) / u :=
          div_le_div_of_nonneg_right (div_le_self hnum hden) hu.le
        _ ≤ (Real.exp 2 * derivativeWeight φ u ^ 2) / u :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) hu.le
        _ = Real.exp 2 * (derivativeWeight φ u ^ 2 / u) := by ring
  rw [integral_const_mul] at hbound
  unfold normFunctional weightEnergy
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (Real.exp 2 *
        ∫ u in Ioi (0 : ℝ), derivativeWeight φ u ^ 2 / u) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (by positivity))
    _ = _ := by ring

end ConditionalGoldbach
