import ConditionalGoldbach.Proofs.DensitySeries
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! A positive majorant for the diagonal term sufficient for the fixed-modulus obstruction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace ConditionalGoldbach

lemma mangoldt_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n : ℕ => (mangoldt n:ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

lemma deriv_logDeriv_zeta_eq_mangoldt_log {s : ℂ} (hs : 1 < s.re) :
    deriv (logDeriv riemannZeta) s =
      LSeries (LSeries.logMul (fun n : ℕ => (mangoldt n:ℂ))) s := by
  have hab : LSeries.abscissaOfAbsConv (fun n : ℕ => (mangoldt n:ℂ)) < s.re :=
    mangoldt_abscissa_le_one.trans_lt (by exact_mod_cast hs)
  have he : LSeries (fun n : ℕ => (mangoldt n:ℂ)) =ᶠ[𝓝 s] fun z => -logDeriv riemannZeta z := by
    filter_upwards [(isOpen_re_gt 1).mem_nhds hs] with z hz
    simpa only [logDeriv_apply,neg_div] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
  have hd := he.deriv_eq
  change deriv (LSeries (fun n : ℕ => (mangoldt n:ℂ))) s = deriv (-logDeriv riemannZeta) s at hd
  rw [LSeries_deriv hab,deriv.neg] at hd
  exact neg_injective hd.symm

lemma diagonalSeries_real_le_zeta_second (N : ℕ) {w : ℝ} (hw : 0 < w) :
    (diagonalSeries N (w:ℂ)).re ≤ (deriv (logDeriv riemannZeta) (1+(w:ℂ))).re := by
  have hRe : 1 < (1+(w:ℂ)).re := by simpa using hw
  have hab : LSeries.abscissaOfAbsConv (fun n : ℕ => (mangoldt n:ℂ)) < (1+(w:ℂ)).re :=
    mangoldt_abscissa_le_one.trans_lt (by exact_mod_cast hRe)
  have hS := LSeriesSummable_logMul_of_lt_re hab
  have hD : Summable (fun n : ℕ => if 0<n ∧ Nat.Coprime n N then
      (mangoldt n:ℂ)^2/(n:ℂ)^(1+(w:ℂ)) else 0) := by
    apply Summable.of_norm
    simpa only [apply_ite norm,norm_zero] using diagonalSeries_summable N (w := (w:ℂ)) hw
  rw [deriv_logDeriv_zeta_eq_mangoldt_log hRe,diagonalSeries,LSeries,
    Complex.re_tsum hD,Complex.re_tsum hS]
  apply Summable.tsum_le_tsum _ (Complex.reCLM.summable hD) (Complex.reCLM.summable hS)
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hΛ : 0 ≤ mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hpow : (n:ℂ)^(1+(w:ℂ)) = (((n:ℝ)^(1+w):ℝ):ℂ) := by
    simpa only [ofReal_natCast,ofReal_add,ofReal_one] using (Complex.ofReal_cpow hn0.le (1+w)).symm
  have hclog : Complex.log (n:ℂ) = (Real.log n:ℂ) := by
    rw [← Complex.ofReal_natCast,Complex.ofReal_log hn0.le]
  rw [LSeries.term_of_ne_zero hn]
  simp only [LSeries.logMul,hclog,hpow]
  change (if 0<n ∧ Nat.Coprime n N then (mangoldt n:ℂ)^2/(((n:ℝ)^(1+w):ℝ):ℂ) else 0).re ≤
    (((Real.log n:ℂ)*(mangoldt n:ℂ))/(((n:ℝ)^(1+w):ℝ):ℂ)).re
  by_cases hc : Nat.Coprime n N
  · rw [if_pos ⟨Nat.pos_of_ne_zero hn,hc⟩]
    simp only [← ofReal_pow,← ofReal_mul,← ofReal_div,ofReal_re]
    change (mangoldt n)^2/(n:ℝ)^(1+w) ≤ Real.log n*mangoldt n/(n:ℝ)^(1+w)
    exact div_le_div_of_nonneg_right (by have hL : mangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log; nlinarith) (by positivity)
  · simp only [hc,and_false,ite_false,zero_re,← ofReal_mul,← ofReal_div,ofReal_re]
    change 0 ≤ Real.log n*mangoldt n/(n:ℝ)^(1+w)
    positivity

end ConditionalGoldbach
