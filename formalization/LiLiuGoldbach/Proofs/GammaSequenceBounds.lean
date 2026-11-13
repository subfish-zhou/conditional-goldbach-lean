import LiLiuGoldbach.Proofs.CharacterGammaFactor
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Uniform majorants for Euler's finite Gamma products. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace LiLiuGoldbach16

lemma real_GammaSeq_le_Gamma {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    Real.GammaSeq x n ≤ Real.Gamma x := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hf : ∀ {y : ℝ}, 0 < y → (Real.log ∘ Real.Gamma) (y+1) =
      (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ring
  have hb := Real.BohrMollerup.ge_logGammaSeq Real.convexOn_log_Gamma hf hx hn
  have hp : 0 < ∏ j ∈ Finset.range (n+1), (x+(j:ℝ)) :=
    Finset.prod_pos (fun j _ => by positivity)
  have hs : 0 < Real.GammaSeq x n := by
    unfold Real.GammaSeq
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hnp _) (by positivity)) hp
  have he : Real.log (Real.GammaSeq x n) = Real.BohrMollerup.logGammaSeq x n := by
    unfold Real.GammaSeq Real.BohrMollerup.logGammaSeq
    rw [Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hnp _).ne' (by positivity)) hp.ne',
      Real.log_mul (Real.rpow_pos_of_pos hnp _).ne' (by positivity), Real.log_rpow hnp]
    rw [Real.log_prod (fun j _ => by positivity)]
  apply (Real.log_le_log_iff hs (Real.Gamma_pos_of_pos hx)).mp
  simpa [Function.comp_apply, Real.Gamma_one, he] using hb

lemma GammaSeq_norm_le_Gamma_re {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.GammaSeq s n‖ ≤ Real.Gamma s.re := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp : 0 < ∏ j ∈ Finset.range (n+1), (s.re+(j:ℝ)) :=
    Finset.prod_pos (fun j _ => by positivity)
  have hb : (∏ j ∈ Finset.range (n+1), (s.re+(j:ℝ))) ≤
      ∏ j ∈ Finset.range (n+1), ‖s+(j:ℂ)‖ := by
    apply Finset.prod_le_prod₀
    · intro j hj; positivity
    · intro j hj
      simpa using (Complex.re_le_norm (s+(j:ℂ)))
  apply le_trans (b := Real.GammaSeq s.re n) ?_ (real_GammaSeq_le_Gamma hs hn)
  unfold Complex.GammaSeq Real.GammaSeq
  rw [norm_div, norm_mul, norm_prod, ← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hnp]
  simp only [Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (by positivity) hp hb

lemma GammaSeq_differentiableAt {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun z => Complex.GammaSeq z n) s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => (n:ℂ)^z * (n.factorial:ℂ)) s :=
    (differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hn))).mul_const _
  have hp : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n+1), (z+(j:ℂ))) s :=
    DifferentiableAt.fun_finset_prod (fun j _ => differentiableAt_id.add_const _)
  apply hd.div hp
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj he
  have := congrArg Complex.re he
  simp only [add_re,natCast_re,zero_re] at this
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

end LiLiuGoldbach16
