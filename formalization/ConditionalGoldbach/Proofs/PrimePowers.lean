module

public import Mathlib.NumberTheory.Chebyshev
public import ConditionalGoldbach.Proofs.Weights

/-! Removal of pairs containing a proper prime power from the weighted correlation. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- The part of the original weighted correlation with at least one nonprime entry.
The original range, coprimality filter, and both weights are retained. -/
def badGoldbachMass (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    if (0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N) ∧
        (¬n.Prime ∨ ¬(N - n).Prime) then
      mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
    else 0

theorem mangoldt_le_log_of_le {n N : ℕ} (hN : 0 < N) (hn : n ≤ N) :
    mangoldt n ≤ Real.log N := by
  by_cases hzero : n = 0
  · subst n
    simpa [mangoldt] using Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hn))

theorem sum_nonprime_mangoldt_eq_psi_sub_theta (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), if ¬n.Prime then mangoldt n else 0) =
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  change (∑ n ∈ Finset.range (N + 1), if ¬n.Prime then mangoldt n else 0) =
    ∑ n ∈ Finset.Ioc 0 N, if ¬n.Prime then mangoldt n else 0
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hn).2)
  · intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_range, Finset.mem_Ioc, not_and] at hn hnot
      omega
    subst n
    simp [mangoldt]

theorem badGoldbachMass_le_psi_sub_theta (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    badGoldbachMass N φ ≤ (2 * Real.log N / N) *
      (Chebyshev.psi N - Chebyshev.theta N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hterm (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      (if (0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N) ∧
          (¬n.Prime ∨ ¬(N - n).Prime) then
        mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
        else 0) ≤
      Real.log N * (if ¬n.Prime then mangoldt n else 0) +
        Real.log N * (if ¬(N - n).Prime then mangoldt (N - n) else 0) := by
    have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hvn : 0 ≤ mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hvm : 0 ≤ mangoldt (N - n) := ArithmeticFunction.vonMangoldt_nonneg
    have hnlog := mangoldt_le_log_of_le hN hnle
    have hmlog := mangoldt_le_log_of_le hN (Nat.sub_le N n)
    have hprod : 0 ≤ mangoldt n * mangoldt (N - n) := mul_nonneg hvn hvm
    have hweight : mangoldt n * mangoldt (N - n) * φ (n / N) *
        φ ((N - n : ℕ) / N) ≤ mangoldt n * mangoldt (N - n) := by
      calc
        _ ≤ mangoldt n * mangoldt (N - n) * φ (n / N) :=
          mul_le_of_le_one_right (mul_nonneg hprod (hφ.nonneg _)) (hφ.le_one _)
        _ ≤ _ := mul_le_of_le_one_right hprod (hφ.le_one _)
    have hleft : mangoldt n * mangoldt (N - n) * φ (n / N) *
        φ ((N - n : ℕ) / N) ≤ Real.log N * mangoldt n := by
      exact hweight.trans (by nlinarith)
    have hright : mangoldt n * mangoldt (N - n) * φ (n / N) *
        φ ((N - n : ℕ) / N) ≤ Real.log N * mangoldt (N - n) := by
      exact hweight.trans (mul_le_mul_of_nonneg_right hnlog hvm)
    have hnpart : 0 ≤ Real.log N * (if ¬n.Prime then mangoldt n else 0) := by
      split_ifs <;> positivity
    have hmpart : 0 ≤ Real.log N * (if ¬(N - n).Prime then mangoldt (N - n) else 0) := by
      split_ifs <;> positivity
    by_cases h : (0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N) ∧
        (¬n.Prime ∨ ¬(N - n).Prime)
    · rw [ite_eq_left h]
      rcases h.2 with hnp | hmp
      · simpa only [ite_eq_left hnp] using le_add_of_le_of_nonneg hleft hmpart
      · simpa only [ite_eq_left hmp] using le_add_of_nonneg_of_le hnpart hright
    · rw [ite_eq_right h]
      exact add_nonneg hnpart hmpart
  have hreflect : (∑ n ∈ Finset.range (N + 1),
      if ¬(N - n).Prime then mangoldt (N - n) else 0) =
      ∑ n ∈ Finset.range (N + 1), if ¬n.Prime then mangoldt n else 0 := by
    simpa using Finset.sum_range_reflect
      (fun n => if ¬n.Prime then mangoldt n else 0) (N + 1)
  unfold badGoldbachMass
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        (Real.log N * (if ¬n.Prime then mangoldt n else 0) +
          Real.log N * (if ¬(N - n).Prime then mangoldt (N - n) else 0)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (inv_nonneg.mpr hNpos.le)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hreflect,
        sum_nonprime_mangoldt_eq_psi_sub_theta]
      ring

theorem badGoldbachMass_le_sqrt (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    badGoldbachMass N φ ≤ 4 * Real.log N ^ 2 / Real.sqrt N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  calc
    _ ≤ (2 * Real.log N / N) * (Chebyshev.psi N - Chebyshev.theta N) :=
      badGoldbachMass_le_psi_sub_theta N hN φ hφ
    _ ≤ (2 * Real.log N / N) * (2 * Real.sqrt N * Real.log N) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le hN1)
        (div_nonneg (mul_nonneg (by norm_num) hlog) hNpos.le)
    _ = _ := by
      field_simp
      have hs := congrArg (fun x : ℝ => 4 * Real.log N ^ 2 * x) (Real.sq_sqrt hNpos.le)
      nlinarith only [hs]


theorem goldbach_le_badGoldbachMass_add_primePairCount (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    goldbach N φ ≤ badGoldbachMass N φ +
      (Real.log N ^ 2 / N) * (PrimePairCount N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  let good : ℕ → Prop := fun n => n.Prime ∧ (N - n).Prime ∧
    (N : ℝ) / 3 ≤ n ∧ (n : ℝ) ≤ 2 * N / 3
  have hind (n : ℕ) : 0 ≤ (if good n then Real.log N ^ 2 else 0) := by
    split_ifs <;> positivity
  have hterm (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      (if 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N then
        mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
        else 0) ≤
      (if (0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N) ∧
          (¬n.Prime ∨ ¬(N - n).Prime) then
        mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
        else 0) + (if good n then Real.log N ^ 2 else 0) := by
    by_cases hc : 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N
    · rw [ite_eq_left hc]
      by_cases hb : ¬n.Prime ∨ ¬(N - n).Prime
      · rw [ite_eq_left ⟨hc, hb⟩]
        exact le_add_of_nonneg_right (hind n)
      · have hbad : ¬((0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N) ∧
            (¬n.Prime ∨ ¬(N - n).Prime)) := fun h => hb h.2
        rw [ite_eq_right hbad, zero_add]
        by_cases hz : φ ((n : ℝ) / N) = 0
        · simp only [hz, mul_zero, zero_mul]
          exact hind n
        · have hs := hφ.mem_support_interval hz
          have hg : good n := by
            have hp : n.Prime ∧ (N - n).Prime := by tauto
            refine ⟨hp.1, hp.2, ?_, ?_⟩
            · have hh := (le_div_iff₀ hNpos).mp hs.1
              linarith
            · have hh := (div_le_iff₀ hNpos).mp hs.2
              linarith
          rw [ite_eq_left hg]
          have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
          have hvn : 0 ≤ mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          have hvm : 0 ≤ mangoldt (N - n) := ArithmeticFunction.vonMangoldt_nonneg
          have hnlog := mangoldt_le_log_of_le hN hnle
          have hmlog := mangoldt_le_log_of_le hN (Nat.sub_le N n)
          have hprod : 0 ≤ mangoldt n * mangoldt (N - n) := mul_nonneg hvn hvm
          calc
            _ ≤ mangoldt n * mangoldt (N - n) * φ (n / N) :=
              mul_le_of_le_one_right (mul_nonneg hprod (hφ.nonneg _)) (hφ.le_one _)
            _ ≤ mangoldt n * mangoldt (N - n) :=
              mul_le_of_le_one_right hprod (hφ.le_one _)
            _ ≤ Real.log N * Real.log N :=
              mul_le_mul hnlog hmlog hvm hlog
            _ = _ := by ring
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.1), zero_add]
      exact hind n
  have hcount : (∑ n ∈ Finset.range (N + 1), if good n then Real.log N ^ 2 else 0) =
      (PrimePairCount N : ℝ) * Real.log N ^ 2 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rfl
  unfold goldbach badGoldbachMass
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
      ((if (0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N) ∧
          (¬n.Prime ∨ ¬(N - n).Prime) then
        mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
        else 0) + (if good n then Real.log N ^ 2 else 0)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (inv_nonneg.mpr hNpos.le)
    _ = _ := by
      rw [Finset.sum_add_distrib, mul_add, hcount]
      ring


end ConditionalGoldbach
