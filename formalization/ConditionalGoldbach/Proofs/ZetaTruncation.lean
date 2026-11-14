module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.AbelSummation
public import ConditionalGoldbach.Proofs.ZetaGrowth

/-! A truncated Euler formula, retaining the fractional-part remainder explicitly. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def zetaFractionTail (s : ℂ) (X : ℝ) : ℂ :=
  ∫ t in Ioi X, ((Int.fract t : ℝ) : ℂ)*(t : ℂ)^(-(s+1))

lemma zetaFractionTail_integrable {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 1 ≤ X) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)*(t : ℂ)^(-(s+1))) (Ioi X) :=
  (zetaFractionIntegral_integrable hs).mono_set (Ioi_subset_Ioi hX)

lemma zetaFractionTail_norm {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 1 ≤ X) :
    ‖zetaFractionTail s X‖ ≤ X^(-s.re)/s.re := by
  have hX0 : 0 < X := by linarith
  unfold zetaFractionTail
  calc
    _ ≤ ∫ t in Ioi X, ‖((Int.fract t : ℝ) : ℂ)*(t : ℂ)^(-(s+1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi X, t^(-s.re-1) := by
      apply integral_mono_ae (zetaFractionTail_integrable hs hX).norm
        (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hX0)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hX0.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t),
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re]
      calc
        _ ≤ 1*t^(-(s.re+1)) := mul_le_mul_of_nonneg_right (Int.fract_lt_one t).le (by positivity)
        _ = _ := by rw [one_mul]; congr 1; ring
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hX0]
      simp only [sub_add_cancel, neg_div_neg_eq]

lemma zetaFractionTail_split {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 1 ≤ X) :
    zetaFractionIntegral s =
      (∫ t in (1 : ℝ)..X, ((Int.fract t : ℝ) : ℂ)*(t : ℂ)^(-(s+1))) + zetaFractionTail s X := by
  rw [zetaFractionIntegral_eq, zetaFractionTail]
  exact (intervalIntegral.integral_interval_add_Ioi (zetaFractionIntegral_integrable hs)
    (zetaFractionTail_integrable hs hX)).symm

lemma zeta_partial_abel (m : ℕ) (hm : 1 ≤ m) (s : ℂ) (hs : s ≠ 0) :
    (∑ n ∈ Finset.Icc 1 m, (n : ℂ)^(-s)) = (m : ℂ)^(1-s) +
      s * ∫ t in (1 : ℝ)..(m : ℝ), (Nat.floor t : ℂ)*(t : ℂ)^(-(s+1)) := by
  let c : ℕ → ℂ := fun n => if n = 0 then 0 else 1
  have hc (n : ℕ) : c n = 1-(if n=0 then 1 else 0) := by by_cases h : n=0 <;> simp [c,h]
  have hsum (n : ℕ) : (∑ k ∈ Finset.Icc 0 n, c k) = n := by
    simp_rw [hc, Finset.sum_sub_distrib]
    simp
  have hd (t : ℝ) (ht : t ∈ Icc (1 : ℝ) m) :
      deriv (fun x : ℝ => (x : ℂ)^(-s)) t = (-s)*(t : ℂ)^(-s-1) :=
    deriv_ofReal_cpow_const (by linarith [ht.1]) (neg_ne_zero.mpr hs)
  have hdif (t : ℝ) (ht : t ∈ Icc (1 : ℝ) m) :
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ)^(-s)) t :=
    (hasDerivAt_ofReal_cpow_const (by linarith [ht.1]) (neg_ne_zero.mpr hs)).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t : ℂ)^(-s-1)) (Icc (1 : ℝ) m) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const t (-s-1)
      (Or.inr (by linarith [ht.1])))).continuousWithinAt
  have hint : IntegrableOn (deriv (fun x : ℝ => (x : ℂ)^(-s))) (Icc (1 : ℝ) m) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).symm) measurableSet_Icc
  have he := sum_mul_eq_sub_integral_mul₀' c (by simp [c]) m hdif hint
  push_cast at he
  rw [hsum] at he
  have hleft : (∑ k ∈ Finset.Icc 0 m, (k : ℂ)^(-s)*c k) =
      ∑ k ∈ Finset.Icc 1 m, (k : ℂ)^(-s) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le m)]
    rw [Finset.sum_insert (by simp)]
    simp only [c, ite_eq_left rfl, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ite_eq_right (by have := (Finset.mem_Icc.mp hk).1; omega), mul_one]
  rw [hleft] at he
  have hpow : (m : ℂ)^(-s)*(m : ℂ) = (m : ℂ)^(1-s) := by
    nth_rw 2 [← Complex.cpow_one (m : ℂ)]
    rw [← Complex.cpow_add _ _ (by exact_mod_cast (show m ≠ 0 by omega))]
    congr 1
    ring
  rw [hpow] at he
  have heint : (∫ t in Ioc (1 : ℝ) (m : ℝ),
      deriv (fun x : ℝ => (x : ℂ)^(-s)) t * ∑ k ∈ Finset.Icc 0 (Nat.floor t), c k) =
      -s * ∫ t in (1 : ℝ)..(m : ℝ), (Nat.floor t : ℂ)*(t : ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hm), ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hd t ⟨ht.1.le,ht.2⟩, hsum]
    rw [show -(s+1)=-s-1 by ring]
    ring
  rw [heint] at he
  rw [he]
  ring

lemma zeta_truncated_formula (m : ℕ) (hm : 1 ≤ m) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (∑ n ∈ Finset.Icc 1 m, (n : ℂ)^(-s)) +
      (m : ℂ)^(1-s)/(s-1) - s*zetaFractionTail s m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hzero : (0 : ℝ) ∉ uIcc (1 : ℝ) m := by
    rw [uIcc_of_le hmR]
    simp
  have hiP : IntervalIntegrable (fun t : ℝ => (t : ℂ)^(-s)) volume 1 m :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hzero)
  have hiF : IntervalIntegrable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)*(t : ℂ)^(-(s+1))) volume 1 m :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hmR).mpr
      ((zetaFractionIntegral_integrable hs).mono_set Ioc_subset_Ioi_self)
  have heq : (∫ t in (1 : ℝ)..(m : ℝ), (Nat.floor t : ℂ)*(t : ℂ)^(-(s+1))) =
      (∫ t in (1 : ℝ)..(m : ℝ), (t : ℂ)^(-s)) -
      (∫ t in (1 : ℝ)..(m : ℝ), ((Int.fract t : ℝ) : ℂ)*(t : ℂ)^(-(s+1))) := by
    rw [← intervalIntegral.integral_sub hiP hiF]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hmR] at ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [ht.1])
    have hfloor : (Nat.floor t : ℝ)+Int.fract t = t := by
      rw [natCast_floor_eq_intCast_floor (by linarith [ht.1])]
      exact Int.floor_add_fract t
    have hc := congrArg Complex.ofReal hfloor
    push_cast at hc
    have hpow : (t : ℂ)*(t : ℂ)^(-(s+1)) = (t : ℂ)^(-s) := by
      nth_rw 1 [← Complex.cpow_one (t : ℂ)]
      rw [← Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp only
    rw [← hpow]
    linear_combination (t : ℂ)^(-(s+1))*hc
  have hP : (∫ t in (1 : ℝ)..(m : ℝ), (t : ℂ)^(-s)) =
      ((m : ℂ)^(1-s)-1)/(1-s) := by
    rw [integral_cpow (Or.inr ⟨by intro he; apply hs1; linear_combination -he,hzero⟩)]
    simp only [show -s+1=1-s by ring, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_natCast]
  have hab := zeta_partial_abel m hm s (Complex.ne_zero_of_re_pos hs)
  rw [heq, hP] at hab
  rw [riemannZeta_fraction_formula hs hs1, zetaFractionTail_split hs hmR, hab]
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [show 1-s = -(s-1) by ring, div_neg]
  field_simp; ring

lemma zeta_partial_three_quarter_bound (m : ℕ) (hm : 1 ≤ m) :
    (∑ n ∈ Finset.Icc 1 m, (n : ℝ)^(-(3/4 : ℝ))) ≤ 4*(m : ℝ)^(1/4 : ℝ) := by
  have ha : AntitoneOn (fun t : ℝ => t^(-(3/4 : ℝ))) (Icc (1 : ℝ) m) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by norm_num)
  have hi := AntitoneOn.sum_le_integral_Ico (f := fun t : ℝ => t^(-(3/4 : ℝ))) hm (by simpa using ha)
  have hshift : (∑ n ∈ Finset.Ico 1 m, ((n+1 : ℕ) : ℝ)^(-(3/4 : ℝ))) =
      ∑ n ∈ Finset.Icc 2 m, (n : ℝ)^(-(3/4 : ℝ)) := by
    rw [Finset.sum_Ico_add' (fun k : ℕ => (k : ℝ)^(-(3/4 : ℝ))) 1 m 1]
    congr 1
  rw [hshift, integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(3/4 : ℝ)))] at hi
  norm_num at hi
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hm, Finset.sum_insert (by simp)]
  norm_num
  linarith

lemma zeta_partial_norm_bound (m : ℕ) (hm : 1 ≤ m) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖∑ n ∈ Finset.Icc 1 m, (n : ℂ)^(-s)‖ ≤ 4*(m : ℝ)^(1/4 : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 m, ‖(n : ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 m, (n : ℝ)^(-(3/4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by linarith
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ ≤ _ := zeta_partial_three_quarter_bound m hm

lemma riemannZeta_three_quarter_growth {hi : ℝ} {s : ℂ}
    (hlo : 3/4 ≤ s.re) (hhi : s.re ≤ hi) (ht : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (5+(4/3)*(hi+1))*(1+|s.im|)^(1/4 : ℝ) := by
  let T : ℝ := |s.im|
  let m : ℕ := Nat.ceil T
  have hT : 1 ≤ T := ht
  have hT0 : 0 < T := by linarith
  have hTm : T ≤ (m : ℝ) := Nat.le_ceil T
  have hmR : (1 : ℝ) ≤ m := hT.trans hTm
  have hm : 1 ≤ m := by exact_mod_cast hmR
  have hmT : (m : ℝ) ≤ 1+T := by have := Nat.ceil_lt_add_one hT0.le; dsimp [m]; linarith
  have hsr : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht
  have hden : 1 ≤ ‖s-1‖ := by
    have := Complex.abs_im_le_norm (s-1)
    simp only [sub_im, one_im, sub_zero] at this
    exact ht.trans this
  have hhi0 : 0 ≤ hi := by linarith
  have hn : ‖s‖ ≤ hi+T := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hsr] at this
    linarith
  have hQ : (m : ℝ)^(1/4 : ℝ) ≤ (1+T)^(1/4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hmT (by norm_num)
  have hpow : ‖(m : ℂ)^(1-s)‖ ≤ (m : ℝ)^(1/4 : ℝ) := by
    rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < m)]
    exact Real.rpow_le_rpow_of_exponent_le hmR (by simp; linarith)
  have hp : (m : ℝ)^(-s.re) ≤ T^(-(3/4 : ℝ)) :=
    (Real.rpow_le_rpow_of_exponent_le hmR (by linarith : -s.re ≤ -(3/4 : ℝ))).trans
      (Real.rpow_le_rpow_of_nonpos hT0 hTm (by norm_num))
  have htail : ‖zetaFractionTail s m‖ ≤ (4/3)*T^(-(3/4 : ℝ)) := by
    calc
      _ ≤ (m : ℝ)^(-s.re)/s.re := zetaFractionTail_norm hsr hmR
      _ ≤ T^(-(3/4 : ℝ))/(3/4) := div_le_div₀ (by positivity) hp (by norm_num) hlo
      _ = _ := by ring
  have hTpow : T*T^(-(3/4 : ℝ)) = T^(1/4 : ℝ) := by
    nth_rw 1 [← Real.rpow_one T]
    rw [← Real.rpow_add hT0]
    norm_num
  have htail' : ‖s*zetaFractionTail s m‖ ≤ (4/3)*(hi+1)*(1+T)^(1/4 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (hi+T)*((4/3)*T^(-(3/4 : ℝ))) := mul_le_mul hn htail (norm_nonneg _) (by positivity)
      _ ≤ ((hi+1)*T)*((4/3)*T^(-(3/4 : ℝ))) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = (4/3)*(hi+1)*(T*T^(-(3/4 : ℝ))) := by ring
      _ = (4/3)*(hi+1)*T^(1/4 : ℝ) := by rw [hTpow]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hT0.le (by linarith : T ≤ 1+T) (by norm_num)) (by positivity)
  rw [zeta_truncated_formula m hm hsr hs1]
  calc
    _ ≤ ‖∑ n ∈ Finset.Icc 1 m, (n : ℂ)^(-s)‖ + ‖(m : ℂ)^(1-s)/(s-1)‖ +
        ‖s*zetaFractionTail s m‖ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 4*(m : ℝ)^(1/4 : ℝ)+(m : ℝ)^(1/4 : ℝ)+(4/3)*(hi+1)*(1+T)^(1/4 : ℝ) := by
      apply add_le_add _ htail'
      apply add_le_add (zeta_partial_norm_bound m hm s hlo)
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) hden).trans hpow
    _ ≤ _ := by nlinarith

lemma riemannZeta_three_quarter_uniform {hi : ℝ} (hhi : hi < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ∈ Icc (3/4) hi →
      ‖riemannZeta w‖ ≤ C*(1+|w.im|)^(1/4 : ℝ) := by
  let K : Set ℂ := (Icc (3/4 : ℝ) hi) ×ℂ (Icc (-1 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn riemannZeta K := by
    intro w hw
    apply (differentiableAt_riemannZeta _).continuousAt.continuousWithinAt
    intro he
    have hh : w.re ≤ hi := hw.1.2
    norm_num [he] at hh
    linarith
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc
  let D : ℝ := 5+(4/3)*(|hi|+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨|B|+D+1, by positivity, fun w hw => ?_⟩
  have hp : 0 ≤ (1+|w.im|)^(1/4 : ℝ) := by positivity
  by_cases ht : 1 ≤ |w.im|
  · have he := riemannZeta_three_quarter_growth hw.1 hw.2 ht
    exact he.trans (mul_le_mul_of_nonneg_right (by dsimp [D]; nlinarith [le_abs_self hi,abs_nonneg B]) hp)
  · have hm : w ∈ K := ⟨hw,abs_le.mp (lt_of_not_ge ht).le⟩
    have hb := hB w hm
    have hp1 : 1 ≤ (1+|w.im|)^(1/4 : ℝ) :=
      Real.one_le_rpow (by linarith [abs_nonneg w.im]) (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ |B|+D+1 by positivity)
    linarith [le_abs_self B]

end ConditionalGoldbach
