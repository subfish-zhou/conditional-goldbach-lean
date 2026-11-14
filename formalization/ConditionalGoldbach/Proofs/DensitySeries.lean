module

public import ConditionalGoldbach.Definitions.Model
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Absolute convergence and holomorphy of the diagonal Dirichlet series. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma LSeriesSummable_mangoldt_sq (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => if Nat.Coprime n N then (mangoldt n : ℂ)^2 else 0) s := by
  have hf := LSeriesSummable_logMul_of_lt_re (f := LSeries.logMul 1)
    (s := s) (by rw [LSeries.abscissaOfAbsConv_logMul, LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs)
  rw [LSeriesSummable, ← summable_norm_iff] at hf ⊢
  refine hf.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => LSeries.norm_term_le (n := n) s ?_)
  change ‖(if Nat.Coprime n N then (mangoldt n : ℂ)^2 else 0)‖ ≤
    ‖Complex.log n * (Complex.log n * 1)‖
  by_cases hn : Nat.Coprime n N
  · rw [ite_eq_left hn]
    simp only [norm_pow, mul_one, norm_mul]
    have hΛ : ‖(mangoldt n : ℂ)‖ ≤ ‖Complex.log n‖ := by
      simpa [mangoldt, abs_of_nonneg, ArithmeticFunction.vonMangoldt_nonneg,
        ← Complex.natCast_log, Real.log_natCast_nonneg]
        using (ArithmeticFunction.vonMangoldt_le_log (n := n))
    nlinarith [norm_nonneg (mangoldt n : ℂ), norm_nonneg (Complex.log n)]
  · simp only [hn, ite_false, norm_zero]
    positivity

lemma diagonalSeries_eq_LSeries (N : ℕ) (w : ℂ) :
    diagonalSeries N w =
      LSeries (fun n : ℕ => if Nat.Coprime n N then (mangoldt n : ℂ)^2 else 0) (1 + w) := by
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · simp only [LSeries.term, ite_false, Nat.pos_iff_ne_zero, hn]
    split_ifs <;> simp_all

lemma diagonalSeries_summable (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => if 0 < n ∧ Nat.Coprime n N then
      ‖(mangoldt n : ℂ)^2 / (n : ℂ) ^ (1 + w)‖ else 0) := by
  have h := (LSeriesSummable_mangoldt_sq N (s := 1 + w) (by simpa using hw)).norm
  apply h.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · simp only [LSeries.term, ite_false, Nat.pos_iff_ne_zero, hn]
    split_ifs <;> simp_all

lemma diagonalSeries_differentiableAt (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (diagonalSeries N) w := by
  have hab : LSeries.abscissaOfAbsConv
      (fun n : ℕ => if Nat.Coprime n N then (mangoldt n : ℂ)^2 else 0) ≤ (1 : ℝ) := by
    exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => LSeriesSummable_mangoldt_sq N hs)
  have ht : (1 : EReal) < ((1 + w).re : ℝ) := by
    exact_mod_cast (show (1 : ℝ) < (1 + w).re by simpa using hw)
  have hd := (LSeries_hasDerivAt (lt_of_le_of_lt hab ht)).differentiableAt
  simpa only [Function.comp_def, ← diagonalSeries_eq_LSeries] using
    hd.comp w ((differentiableAt_const (1 : ℂ)).add differentiableAt_id)

lemma diagonalSeries_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (diagonalSeries N) {w | 0 < w.re} :=
  fun _ hw => (diagonalSeries_differentiableAt N hw).differentiableWithinAt

end ConditionalGoldbach
