import LiLiuGoldbach.Proofs.SpectralCompletionUniform

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

/-- The real part of the quaternionic quadratic records the full imaginary radius. -/
theorem quaternion_quadratic_re (q : Quaternion ℝ) :
    (q * (1 - q)).re = q.re * (1 - q.re) + ‖q - (q.re : Quaternion ℝ)‖ ^ 2 := by
  have hn := Quaternion.normSq_eq_norm_mul_self q.im
  rw [Quaternion.normSq_def'] at hn
  simp only [Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im,
    zero_pow (by decide : 2 ≠ 0), zero_add] at hn
  rw [Quaternion.sub_re_self]
  simp only [Quaternion.re_mul, Quaternion.re_sub, Quaternion.re_one, Quaternion.imI_sub,
    Quaternion.imI_one, Quaternion.imJ_sub, Quaternion.imJ_one, Quaternion.imK_sub, Quaternion.imK_one]
  nlinarith

theorem quaternion_critical_quadratic (q : Quaternion ℝ) (d : ℝ)
    (hcrit : q.re = 1 / 2) (hnorm : ‖q - (q.re : Quaternion ℝ)‖ ^ 2 = (d - 1) / 4) :
    q * (1 - q) = ((d / 4 : ℝ) : Quaternion ℝ) := by
  have hre := quaternion_quadratic_re q
  ext
  · simp only [Quaternion.re_coe]
    rw [hre, hnorm, hcrit]
    ring
  all_goals simp [hcrit, -Quaternion.coe_div, -Quaternion.coe_inv] <;> ring

theorem quaternion_quadratic_three_cases (q : Quaternion ℝ) (d : ℝ) (hd : 0 < d) :
    q * (1 - q) = ((d / 4 : ℝ) : Quaternion ℝ) ↔
      (1 < d ∧ q.re = 1 / 2 ∧ ‖q - (q.re : Quaternion ℝ)‖ = Real.sqrt (d - 1) / 2) ∨
      (d = 1 ∧ q = 1 / 2) ∨
      (0 < d ∧ d < 1 ∧
        (q = ((1 / 2 - Real.sqrt (1 - d) / 2 : ℝ) : Quaternion ℝ) ∨
         q = ((1 / 2 + Real.sqrt (1 - d) / 2 : ℝ) : Quaternion ℝ))) := by
  have hhalf : (1 / 2 : Quaternion ℝ) = ((1 / 2 : ℝ) : Quaternion ℝ) := by
    rw [Quaternion.coe_div]; rfl
  constructor
  · intro hroot
    have hre := congrArg (fun q : Quaternion ℝ => q.re) hroot
    rw [quaternion_quadratic_re, Quaternion.re_coe] at hre
    rcases lt_trichotomy d 1 with hlt | heq | hgt
    · have hcrit : q.re ≠ 1 / 2 := by
        intro heq
        rw [heq] at hre
        nlinarith [sq_nonneg ‖q - (q.re : Quaternion ℝ)‖]
      have hreal := quaternion_quadratic_real_of_off_critical q (d / 4) hroot hcrit
      have hxeq : q.re * (1 - q.re) = d / 4 := by
        rw [hreal] at hroot
        have hh := congrArg (fun q : Quaternion ℝ => q.re) hroot
        simpa [-Quaternion.coe_div, -Quaternion.coe_inv] using hh
      have hs := Real.sq_sqrt (show 0 ≤ 1 - d by linarith)
      have hsq : (2 * q.re - 1) ^ 2 = Real.sqrt (1 - d) ^ 2 := by nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hpos | hneg
      · exact Or.inr (Or.inr ⟨hd, hlt, Or.inr (by rw [hreal]; congr 1; linarith)⟩)
      · exact Or.inr (Or.inr ⟨hd, hlt, Or.inl (by rw [hreal]; congr 1; linarith)⟩)
    · have hcrit := quaternion_quadratic_critical_of_bound q (d / 4) hroot (by rw [heq])
      have hn : ‖q - (q.re : Quaternion ℝ)‖ = 0 := by
        nlinarith [norm_nonneg (q - (q.re : Quaternion ℝ))]
      have hreal := sub_eq_zero.1 (norm_eq_zero.1 hn)
      exact Or.inr (Or.inl ⟨heq, by rw [hreal, hcrit, hhalf]⟩)
    · have hcrit := quaternion_quadratic_critical_of_bound q (d / 4) hroot (by linarith)
      have hs := Real.sq_sqrt (show 0 ≤ d - 1 by linarith)
      refine Or.inl ⟨hgt, hcrit, ?_⟩
      apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1
      nlinarith
  · rintro (⟨hgt, hcrit, hn⟩ | ⟨rfl, rfl⟩ | ⟨_, hlt, hq | hq⟩)
    · apply quaternion_critical_quadratic q d hcrit
      rw [hn]
      have hs := Real.sq_sqrt (show 0 ≤ d - 1 by linarith)
      nlinarith
    · rw [hhalf]
      apply quaternion_critical_quadratic
      · rfl
      · simp only [Quaternion.re_coe, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
    all_goals
      rw [hq]
      have hs := Real.sq_sqrt (show 0 ≤ 1 - d by linarith)
      have hh : (1 / 2 - Real.sqrt (1 - d) / 2) * (1 - (1 / 2 - Real.sqrt (1 - d) / 2)) = d / 4 ∧
          (1 / 2 + Real.sqrt (1 - d) / 2) * (1 - (1 / 2 + Real.sqrt (1 - d) / 2)) = d / 4 := by
        constructor <;> nlinarith
      first
      | simpa only [Quaternion.coe_mul, Quaternion.coe_sub, Quaternion.coe_one] using
          congrArg (fun x : ℝ => (x : Quaternion ℝ)) hh.1
      | simpa only [Quaternion.coe_mul, Quaternion.coe_sub, Quaternion.coe_one] using
          congrArg (fun x : ℝ => (x : Quaternion ℝ)) hh.2

theorem proposition_6_3_three_cases (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (q : Quaternion ℝ) :
    spectralQuaternion N (residualOperator ha N) q = 0 ↔
      ∃ j : ℕ, eigenvalues (residualOperator ha N) j ≠ 0 ∧
        let d := spectralRootParameter N (eigenvalues (residualOperator ha N) j)
        (1 < d ∧ q.re = 1 / 2 ∧ ‖q - (q.re : Quaternion ℝ)‖ = Real.sqrt (d - 1) / 2) ∨
        (d = 1 ∧ q = 1 / 2) ∨
        (0 < d ∧ d < 1 ∧
          (q = ((1 / 2 - Real.sqrt (1 - d) / 2 : ℝ) : Quaternion ℝ) ∨
           q = ((1 / 2 + Real.sqrt (1 - d) / 2 : ℝ) : Quaternion ℝ))) := by
  have hparam := large_parameters hlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hδ := spectralScale_pos N hNpos (singularSeries_pos N) hparam.2.1
  have hT := (proposition_5_3 N hN hlarge hGRH ha).2.2.2.2.2.1
  rw [spectralQuaternion_eq_zero_iff N _ hT hδ.ne' q]
  apply exists_congr
  intro j
  apply and_congr_right
  intro hμ
  have hd : 0 < spectralRootParameter N (eigenvalues (residualOperator ha N) j) :=
    div_pos (sq_pos_of_pos hδ) (sq_pos_of_ne_zero hμ)
  have hr : spectralScale N ^ 2 / (4 * eigenvalues (residualOperator ha N) j ^ 2) =
      spectralRootParameter N (eigenvalues (residualOperator ha N) j) / 4 := by
    unfold spectralRootParameter
    ring
  rw [hr]
  exact quaternion_quadratic_three_cases q _ hd

end LiLiuGoldbach16
