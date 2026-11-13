import ConditionalGoldbach.Proofs.Main

/-! Relative error consequences of the exact quadratic form and the spectral dictionary. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

/-- The relative scale in Lemma 7.5; its proof is entirely scalar algebra. -/
theorem spectralScale_relative_bound (N : ℕ) (hN : 0 < (N : ℝ))
    (hS : 0 < singularSeries N) (hlog : 0 < Real.log N)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    spectralScale N / (2 * Real.sqrt (η * (1 - η)) * singularSeries N) ≤
      Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)) := by
  have hprod : 0 < η * (1 - η) := mul_pos hη (by linarith)
  have hroot : 0 < Real.sqrt (η * (1 - η)) := Real.sqrt_pos.2 hprod
  have hr : 0 ≤ Real.log N ^ 3 / (N * η * singularSeries N) := by positivity
  have heq : (2 * Real.sqrt (η * (1 - η)) * singularSeries N *
      Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N))) ^ 2 =
      4 * (1 - η) * spectralScale N ^ 2 := by
    simp only [mul_pow]
    rw [Real.sq_sqrt hprod.le, Real.sq_sqrt hr, spectralScale_sq N hN hS.le hlog.le]
    field_simp
    ring
  apply (div_le_iff₀ (by positivity :
    0 < 2 * Real.sqrt (η * (1 - η)) * singularSeries N)).2
  have hδ := spectralScale_pos N hN hS hlog
  have haux : 0 ≤ (3 - 4 * η) * spectralScale N ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hn : 0 ≤ 2 * Real.sqrt (η * (1 - η)) * singularSeries N *
      Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)) := by positivity
  nlinarith [sq_nonneg (spectralScale N -
    2 * Real.sqrt (η * (1 - η)) * singularSeries N *
      Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)))]

theorem lemma_7_5 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
      Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
      ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → SpectralZeroFree N (alpha N) ha η →
      |goldbach N φ - weightMass φ * singularSeries N| / (weightMass φ * singularSeries N) ≤
        C * Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)) := by
  let A := Real.exp 2 * weightEnergy φ
  let m := weightMass φ
  have hm : 0 < m := weightMass_pos hφ
  have hA : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (weightEnergy_nonneg _)
  refine ⟨A / m + 1, by positivity, ?_⟩
  intro N hNZ hN hlarge hGRH ha η hη hη' hz
  have hp := large_parameters hlarge
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hS := singularSeries_pos N
  have hroot : 0 < Real.sqrt (η * (1 - η)) :=
    Real.sqrt_pos.2 (mul_pos hη (by linarith))
  have hnorm := ((theorem_6_1 N hN hlarge hGRH ha).2.1 η hη (by linarith)).1 hz
  have herr : |goldbach N φ - m * singularSeries N| ≤
      A * (spectralScale N / (2 * Real.sqrt (η * (1 - η)))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hnorm hA)
    simpa only [A, m, abs_sub_comm] using
      theorem_7_1_uniform N hN hlarge hGRH φ hφ ha
  calc
    |goldbach N φ - weightMass φ * singularSeries N| /
        (weightMass φ * singularSeries N)
      ≤ (A * (spectralScale N / (2 * Real.sqrt (η * (1 - η))))) /
          (m * singularSeries N) := div_le_div_of_nonneg_right herr (mul_pos hm hS).le
    _ = (A / m) * (spectralScale N /
          (2 * Real.sqrt (η * (1 - η)) * singularSeries N)) := by ring
    _ ≤ (A / m) * Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)) :=
      mul_le_mul_of_nonneg_left (spectralScale_relative_bound N hNr hS hp.2.1 η hη hη')
        (div_nonneg hA hm.le)
    _ ≤ (A / m + 1) * Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)


theorem lemma_7_5_asymptotic (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ, ∀ (_ : NeZero N), Even N → Real.exp 10 < (N : ℝ) → GRH N →
        ∀ ha : alpha N < beta, ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
          SpectralZeroFree N (alpha N) ha η →
          B ≤ N * η * singularSeries N / Real.log N ^ 3 →
          |goldbach N φ / (weightMass φ * singularSeries N) - 1| < ε := by
  intro ε hε
  obtain ⟨C, hC, herr⟩ := lemma_7_5 φ hφ
  let B := (C / ε) ^ 2 + 1
  refine ⟨B, by positivity, ?_⟩
  intro N hNZ hN hlarge hGRH ha η hη hη' hz hB
  have hp := large_parameters hlarge
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hS := singularSeries_pos N
  have hm := weightMass_pos hφ
  have hlog : 0 < Real.log N ^ 3 := pow_pos hp.2.1 _
  have hden : 0 < (N : ℝ) * η * singularSeries N := by positivity
  have hBmul : B * Real.log N ^ 3 ≤ (N : ℝ) * η * singularSeries N :=
    (le_div_iff₀ hlog).1 hB
  have hCB : C ^ 2 < ε ^ 2 * B := by
    dsimp [B]
    have hcanc : ε ^ 2 * (C / ε) ^ 2 = C ^ 2 := by field_simp
    nlinarith [sq_pos_of_pos hε]
  have hsquared : C ^ 2 * Real.log N ^ 3 < ε ^ 2 * (N * η * singularSeries N) :=
    calc
      _ < ε ^ 2 * B * Real.log N ^ 3 := mul_lt_mul_of_pos_right hCB hlog
      _ = ε ^ 2 * (B * Real.log N ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hBmul (sq_nonneg _)
  have hratio : C ^ 2 * (Real.log N ^ 3 / (N * η * singularSeries N)) < ε ^ 2 := by
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ hden).2 hsquared
  have hsqrt := Real.sq_sqrt (show 0 ≤ Real.log N ^ 3 / (N * η * singularSeries N) by positivity)
  have hsmall : C * Real.sqrt (Real.log N ^ 3 / (N * η * singularSeries N)) < ε := by
    nlinarith [Real.sqrt_nonneg (Real.log N ^ 3 / (N * η * singularSeries N))]
  have heq : |goldbach N φ / (weightMass φ * singularSeries N) - 1| =
      |goldbach N φ - weightMass φ * singularSeries N| / (weightMass φ * singularSeries N) := by
    rw [div_sub_one (mul_pos hm hS).ne', abs_div, abs_of_pos (mul_pos hm hS)]
  rw [heq]
  exact (herr N hNZ hN hlarge hGRH ha η hη hη' hz).trans_lt hsmall

end ConditionalGoldbach
