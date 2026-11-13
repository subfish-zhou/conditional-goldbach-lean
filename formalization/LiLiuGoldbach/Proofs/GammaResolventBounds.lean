import LiLiuGoldbach.Proofs.CharacterGammaFactor
import Mathlib.Analysis.PSeries

/-! Summable quantitative bounds for differences of Gamma resolvents. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace LiLiuGoldbach16

lemma gamma_resolvent_norm_bound (u v : ℂ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hu : a ≤ u.re) (hv : a ≤ v.re) (n : ℕ) :
    ‖1/(v+(n:ℂ))-1/(u+(n:ℂ))‖ ≤ (‖u-v‖/a^2) * (1/((n:ℝ)+1)^2) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hual : a*((n:ℝ)+1) ≤ ‖u+(n:ℂ)‖ := by
    have hh := Complex.re_le_norm (u+(n:ℂ))
    simp only [add_re,natCast_re] at hh
    nlinarith
  have hval : a*((n:ℝ)+1) ≤ ‖v+(n:ℂ)‖ := by
    have hh := Complex.re_le_norm (v+(n:ℂ))
    simp only [add_re,natCast_re] at hh
    nlinarith
  have hun : u+(n:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hual)
  have hvn : v+(n:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hval)
  have he : 1/(v+(n:ℂ))-1/(u+(n:ℂ)) = (u-v)/((v+(n:ℂ))*(u+(n:ℂ))) := by
    field_simp
    ring
  rw [he,norm_div,norm_mul]
  have hden : a^2*((n:ℝ)+1)^2 ≤ ‖v+(n:ℂ)‖*‖u+(n:ℂ)‖ := by
    nlinarith [mul_le_mul hval hual (by positivity : 0 ≤ a*((n:ℝ)+1)) (norm_nonneg (v+(n:ℂ)))]
  calc
    _ ≤ ‖u-v‖/(a^2*((n:ℝ)+1)^2) := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
    _ = _ := by rw [div_mul_eq_div_div]; ring

lemma gamma_resolvent_summable_norm {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Summable (fun n : ℕ => ‖1/(v+(n:ℂ))-1/(u+(n:ℂ))‖) := by
  let a : ℝ := min 1 (min u.re v.re)
  have ha : 0 < a := lt_min zero_lt_one (lt_min hu hv)
  have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
  exact (hs.mul_left (‖u-v‖/a^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
    (gamma_resolvent_norm_bound u v a ha (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)))

lemma sum_one_div_nat_add_one_sq_le (n : ℕ) :
    ∑ j ∈ Finset.range n, 1/((j:ℝ)+1)^2 ≤ 2-2/((n:ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hstep : 1/((n:ℝ)+1)^2 ≤ 2/((n:ℝ)+1)-2/((n:ℝ)+2) := by
      apply (div_le_iff₀ (by positivity : 0 < ((n:ℝ)+1)^2)).mpr
      field_simp
      nlinarith
    have he : (n:ℝ)+1+1 = (n:ℝ)+2 := by ring
    rw [he]
    linarith

end LiLiuGoldbach16
