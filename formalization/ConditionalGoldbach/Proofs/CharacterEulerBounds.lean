module

public import ConditionalGoldbach.Proofs.CharacterEulerCorrection

/-! Uniform conductor corrections on the closed right half of the critical strip. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace ConditionalGoldbach
attribute [local instance] conductorNeZero

lemma sum_log_primeFactors_le_log (N : ℕ) (hN : 0 < N) :
    ∑ p ∈ N.primeFactors, Real.log p ≤ Real.log N := by
  have hp : ∀p ∈ N.primeFactors, (0:ℝ) < p := by
    intro p hp; exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (Finset.prod_pos hp)
  have hh : (∏ p ∈ N.primeFactors, p) ≤ N := Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  have hhR := (Nat.cast_le (α := ℝ)).mpr hh
  simpa only [Nat.cast_prod] using hhR

lemma euler_correction_term_bound {d : ℕ} [NeZero d] (χ : Character d)
    {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : 1/2 ≤ u.re) :
    ‖χ p*(Real.log p:ℂ)/((p:ℂ)^u-χ p)‖ ≤ 4*Real.log p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by positivity
  have hpow : (5/4:ℝ) ≤ ‖(p:ℂ)^u‖ := by
    rw [← Complex.ofReal_natCast p,Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have hs : 5/4 ≤ Real.sqrt 2 := by
      have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have := Real.sqrt_nonneg (2:ℝ)
      nlinarith
    calc
      (5/4:ℝ) ≤ Real.sqrt 2 := hs
      _ = (2:ℝ)^(1/2:ℝ) := Real.sqrt_eq_rpow _
      _ ≤ (p:ℝ)^(1/2:ℝ) := Real.rpow_le_rpow (by norm_num) hp2 (by norm_num)
      _ ≤ (p:ℝ)^u.re := Real.rpow_le_rpow_of_exponent_le (by linarith) hu
  have hden : (1/4:ℝ) ≤ ‖(p:ℂ)^u-χ p‖ := by
    have hh := norm_sub_norm_le ((p:ℂ)^u) (χ p)
    have hχ := χ.norm_le_one p
    linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  calc
    _ ≤ Real.log p / ‖(p:ℂ)^u-χ p‖ := by
      gcongr
      exact mul_le_of_le_one_left hlog (χ.norm_le_one p)
    _ ≤ Real.log p/(1/4:ℝ) := div_le_div_of_nonneg_left hlog (by norm_num) hden
    _ = _ := by ring

lemma eulerCorrection_norm_le {N : ℕ} [NeZero N] (χ : Character N)
    {u : ℂ} (hu : 1/2 ≤ u.re) :
    ‖eulerCorrection χ u‖ ≤ 4*Real.log N := by
  classical
  unfold eulerCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ N.primeFactors, 4*Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpc : p ∣ χ.conductor
      · simp only [hpc,not_true_eq_false,ite_false,norm_zero]
        positivity
      · simp only [hpc,not_false_eq_true,ite_true]
        exact euler_correction_term_bound χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hu
    _ = 4*(∑ p ∈ N.primeFactors, Real.log p) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log N (NeZero.pos N)) (by norm_num)

end ConditionalGoldbach
