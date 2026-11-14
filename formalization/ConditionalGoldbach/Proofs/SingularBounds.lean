module

public import ConditionalGoldbach.Proofs.SingularDensity
public import ConditionalGoldbach.Proofs.Elementary

/-! Arithmetic comparison of the source singular series with N / φ(N). -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
open MathlibNt.SieveTheory.SingularSeries hiding singularSeries

lemma totient_ratio_prod (N : ℕ) (hN : 0 < N) :
    (N : ℝ) / N.totient = ∏ p ∈ N.primeFactors, (p : ℝ) / (p - 1) := by
  have hφ : (N.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have hp : ∀ p ∈ N.primeFactors, (p : ℝ) - 1 ≠ 0 := by
    intro p hp
    have hge : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have he := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors N)
  push_cast at he
  have he' : (N.totient : ℝ) * (∏ p ∈ N.primeFactors, (p : ℝ)) =
      N * ∏ p ∈ N.primeFactors, ((p : ℝ)-1) := by
    convert he using 2
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.one_le_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt), Nat.cast_one]
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hφ (Finset.prod_ne_zero_iff.mpr hp)).2
  linear_combination -he'

lemma oddPrimeFactors_eq_erase_two (N : ℕ) :
    N.primeFactors.filter (fun p => 2 < p) = N.primeFactors.erase 2 := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hp, hgt⟩
    exact ⟨ne_of_gt hgt, hp⟩
  · rintro ⟨hne, hp⟩
    exact ⟨hp, lt_of_le_of_ne (Nat.prime_of_mem_primeFactors hp).two_le hne.symm⟩

lemma totient_ratio_odd_prod (N : ℕ) (hN : Even N) (hpos : 0 < N) :
    (N : ℝ) / N.totient =
      2 * ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (p : ℝ)/(p-1) := by
  have h2 : 2 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hN.two_dvd, hpos.ne'⟩
  rw [totient_ratio_prod N hpos, oddPrimeFactors_eq_erase_two,
    ← Finset.mul_prod_erase _ _ h2]
  norm_num

lemma liuUniversalProduct_le_primeFactors (N : ℕ) :
    liuUniversalProduct ≤ ∏ p ∈ N.primeFactors.filter (fun p => 2 < p),
      (1 + liuBaseDeviation p) := by
  apply le_of_tendsto multipliable_one_add_liuBaseDeviation.hasProd
  filter_upwards [eventually_ge_atTop (N.primeFactors.filter (fun p => 2 < p))] with s hs
  exact Finset.prod_le_prod_of_subset_of_le_one₀ hs
    (fun p hp => (one_add_liuBaseDeviation_pos p).le)
    (fun p hp hnot => one_add_liuBaseDeviation_le_one p)

lemma singularSeries_lower_totient (N : ℕ) (hN : Even N) (hpos : 0 < N) :
    C2 * N / N.totient ≤ singularSeries N := by
  rw [mul_div_assoc, totient_ratio_odd_prod N hN hpos]
  unfold singularSeries liuSingularSeries liuCorrection C2
  have hprod : (∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (p : ℝ)/(p-1)) ≤
      ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), liuCorrectionFactor p := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      exact div_nonneg (by positivity) (by linarith)
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      unfold liuCorrectionFactor
      apply (div_le_div_iff₀ (by linarith) (by linarith)).2
      nlinarith
  nlinarith [liuUniversalProduct_nonneg]

lemma singularSeries_upper_totient (N : ℕ) (hN : Even N) (hpos : 0 < N) :
    singularSeries N ≤ (N : ℝ)/N.totient := by
  have hbound := mul_le_mul_of_nonneg_left (liuUniversalProduct_le_primeFactors N)
    (liuCorrection_pos N).le
  have he : liuCorrection N *
      (∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + liuBaseDeviation p)) =
      ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (p : ℝ)/(p-1) := by
    unfold liuCorrection
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 := (Finset.mem_filter.mp hp).2
    have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    rw [one_add_liuBaseDeviation_eq_baseFactor hprime hp2, liuCorrectionFactor,
      ← liuLocalFactor_of_dvd hp2 (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
    simp [liuLocalFactor, Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1]
  rw [he] at hbound
  rw [totient_ratio_odd_prod N hN hpos]
  exact mul_le_mul_of_nonneg_left hbound (by norm_num)

end ConditionalGoldbach
