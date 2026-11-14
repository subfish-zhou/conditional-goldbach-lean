module

public import ConditionalGoldbach.Proofs.LFunctionDomain
public import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
public import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

/-! Quantitative L-function bounds used by the zero-free disk estimate. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma LFunction_polynomial_bound {q : ℕ} [NeZero q] (χ : Character q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) : ‖χ.LFunction s‖ ≤ q * (1+‖s‖/s.re) := by
  have h := DirichletLConditionalValueSeries.norm_orderedValueSeries_sub_sum_range_le χ hχ s hs
    (m := 1) (by norm_num)
  rw [DirichletLConditionalValueSeries.orderedValueSeries_eq_LFunction_of_re_pos χ hχ s hs] at h
  have hz : χ (0 : ZMod q) = 0 := by
    simpa using DirichletLConditionalValueSeries.character_nat_zero_of_ne_one χ hχ
  simpa [hz] using h

lemma LFunction_sub_one_norm_bound {q : ℕ} [NeZero q] (χ : Character q)
    (s : ℂ) (hs : 1 < s.re) : ‖χ.LFunction s - 1‖ ≤ 1/(s.re-1) := by
  have hsumm := χ.LSeriesSummable_of_one_lt_re hs
  have hsummnorm := hsumm.norm
  have htail : Summable (fun n : ℕ => LSeries.term (fun n : ℕ => χ n) s (n+2)) :=
    (summable_nat_add_iff 2).mpr hsumm
  have hseries : χ.LFunction s - 1 = ∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) s (n+2) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    have he := hsumm.sum_add_tsum_nat_add 2
    have hp : (∑ k ∈ Finset.range 2, LSeries.term (fun n : ℕ => χ n) s k) = 1 := by
      norm_num [Finset.sum_range_succ, LSeries.term]
    rw [hp] at he
    change (∑' n, LSeries.term (fun n : ℕ => χ n) s n) - 1 = _
    rw [← he]
    ring
  have hreal : Summable (fun n : ℕ => (n : ℝ)^(-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htailreal : Summable (fun n : ℕ => ((n+2 : ℕ) : ℝ)^(-s.re)) :=
    (summable_nat_add_iff 2).mpr hreal
  have hsumtail : (∑' n : ℕ, ((n+2 : ℕ) : ℝ)^(-s.re)) ≤ 1/(s.re-1) := by
    have he := hreal.sum_add_tsum_nat_add 2
    have hp : (∑ k ∈ Finset.range 2, (k : ℝ)^(-s.re)) = 1 := by
      norm_num [Finset.sum_range_succ, Real.zero_rpow (by linarith : -s.re ≠ 0)]
    rw [hp] at he
    have hb := AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le s.re hs
    rw [← he] at hb
    linarith
  rw [hseries]
  apply (norm_tsum_le_tsum_norm htail.norm).trans
  apply (htail.norm.tsum_le_tsum _ htailreal).trans hsumtail
  intro n
  have hn : 0 < n+2 := by omega
  have hnR : 0 < ((n+2 : ℕ) : ℝ) := by exact_mod_cast hn
  simp only [LSeries.term, ne_of_gt hn, ite_false, norm_mul, norm_inv,
    Complex.norm_natCast_cpow_of_pos hn, Real.rpow_neg hnR.le, div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg hnR.le _)) (χ.norm_le_one _)

lemma LFunction_right_lower_bound {q : ℕ} [NeZero q] (χ : Character q)
    (s : ℂ) (hs : 3 ≤ s.re) : (1/2 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have hb := LFunction_sub_one_norm_bound χ s (by linarith)
  have hi : 1/(s.re-1) ≤ (1/2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have htriangle : 1 ≤ ‖χ.LFunction s-1‖ + ‖χ.LFunction s‖ := by
    have h := norm_sub_le (χ.LFunction s) (χ.LFunction s-1)
    simpa only [sub_sub_cancel, norm_one, norm_sub_rev, add_comm] using h
  linarith

end ConditionalGoldbach
