module

public import ConditionalGoldbach.Proofs.DensityConvergence

/-! Multiplicative coefficients of the density Euler product. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff LSeries.notation
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
open MathlibNt.SieveTheory.SingularSeries hiding singularSeries

def densityMultiplier (N k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors.filter (fun p => 2 < p ∧ ¬p ∣ N), liuCorrectionFactor p

lemma densityMultiplier_pos (N k : ℕ) : 0 < densityMultiplier N k := by
  apply Finset.prod_pos
  intro p hp
  exact liuCorrectionFactor_pos (Finset.mem_filter.mp hp).2.1

lemma densityMultiplier_one (N : ℕ) : densityMultiplier N 1 = 1 := by
  simp [densityMultiplier]

lemma oddPrimeFactors_mul_disjoint (N k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (k*N).primeFactors.filter (fun p => 2 < p) =
      N.primeFactors.filter (fun p => 2 < p) ∪
        k.primeFactors.filter (fun p => 2 < p ∧ ¬p ∣ N) := by
  have hN0 := hN.ne'
  have hk0 := hk.ne'
  have hkN0 := (Nat.mul_pos hk hN).ne'
  ext p
  simp only [Finset.mem_filter, Finset.mem_union, Nat.mem_primeFactors]
  by_cases hp : p.Prime
  · rw [hp.dvd_mul]
    tauto
  · simp [hp]

lemma oddPrimeFactors_mul_disjointness (N k : ℕ) :
    Disjoint (N.primeFactors.filter (fun p => 2 < p))
      (k.primeFactors.filter (fun p => 2 < p ∧ ¬p ∣ N)) := by
  apply Finset.disjoint_left.mpr
  intro p hpN hpk
  exact (Finset.mem_filter.mp hpk).2.2
    (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hpN).1)

lemma singularSeries_mul_factorization (N k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    singularSeries (k*N) = singularSeries N * densityMultiplier N k := by
  unfold singularSeries liuSingularSeries liuCorrection densityMultiplier
  rw [oddPrimeFactors_mul_disjoint N k hN hk,
    Finset.prod_union (oddPrimeFactors_mul_disjointness N k)]
  ring

lemma densityMultiplier_mul {k l : ℕ} (N : ℕ) (hkl : Nat.Coprime k l)
    (hk : 0 < k) (hl : 0 < l) :
    densityMultiplier N (k*l) = densityMultiplier N k * densityMultiplier N l := by
  unfold densityMultiplier
  rw [Nat.primeFactors_mul hk.ne' hl.ne', Finset.filter_union]
  apply Finset.prod_union
  exact hkl.disjoint_primeFactors.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma densityMultiplier_prime_pow (N p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    densityMultiplier N (p^e) = if 2 < p ∧ ¬p ∣ N then liuCorrectionFactor p else 1 := by
  unfold densityMultiplier
  rw [Nat.primeFactors_prime_pow he.ne' hp]
  rw [Finset.filter_singleton]
  by_cases hh : 2 < p ∧ ¬p ∣ N <;> simp [hh]

def densityMultiplicativeTerm (N : ℕ) (w : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 0 else (densityMultiplier N k : ℂ) / (k : ℂ)^w

lemma densityMultiplicativeTerm_zero (N : ℕ) (w : ℂ) : densityMultiplicativeTerm N w 0 = 0 := by
  simp [densityMultiplicativeTerm]

lemma densityMultiplicativeTerm_one (N : ℕ) (w : ℂ) : densityMultiplicativeTerm N w 1 = 1 := by
  simp [densityMultiplicativeTerm, densityMultiplier_one]

lemma densityMultiplicativeTerm_mul {k l : ℕ} (N : ℕ) (w : ℂ) (hkl : Nat.Coprime k l) :
    densityMultiplicativeTerm N w (k*l) =
      densityMultiplicativeTerm N w k * densityMultiplicativeTerm N w l := by
  by_cases hk : k = 0
  · simp [hk, densityMultiplicativeTerm_zero]
  by_cases hl : l = 0
  · simp [hl, densityMultiplicativeTerm_zero]
  simp only [densityMultiplicativeTerm, hk, hl, Nat.mul_eq_zero, or_self, ite_false,
    densityMultiplier_mul N hkl (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl),
    Complex.ofReal_mul, Nat.cast_mul]
  rw [show ((k : ℂ)*(l : ℂ))^w = (k : ℂ)^w*(l : ℂ)^w by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg l) w]
  ring

lemma densitySeries_term_factorization (N : ℕ) (hN : 0 < N) (w : ℂ) (k : ℕ) :
    (if 0 < k then (singularSeries (k*N) : ℂ)/(k : ℂ)^w else 0) =
      (singularSeries N : ℂ) * densityMultiplicativeTerm N w k := by
  by_cases hk : k = 0
  · simp [hk, densityMultiplicativeTerm_zero]
  · rw [ite_eq_left (Nat.pos_of_ne_zero hk), singularSeries_mul_factorization N k hN (Nat.pos_of_ne_zero hk)]
    simp [densityMultiplicativeTerm, hk, mul_div_assoc]

lemma densityMultiplicativeTerm_summable_norm (N : ℕ) (hN : Even N) (hpos : 0 < N)
    {w : ℂ} (hw : 1 < w.re) :
    Summable (fun k => ‖densityMultiplicativeTerm N w k‖) := by
  have hn : ‖(singularSeries N : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr
    (Complex.ofReal_ne_zero.mpr (singularSeries_pos N).ne')
  have hf := (densitySeries_summable_norm N hN hpos hw).mul_right (‖(singularSeries N : ℂ)‖⁻¹)
  apply hf.congr
  intro k
  have he := congrArg norm (densitySeries_term_factorization N hpos w k)
  simp only [norm_mul] at he
  by_cases hk : 0 < k
  · rw [ite_eq_left hk] at he ⊢
    rw [he]
    field_simp
  · have hk0 : k = 0 := by omega
    subst k
    simp [densityMultiplicativeTerm_zero]

lemma densitySeries_eq_multiplier_tsum (N : ℕ) (hN : 0 < N) (w : ℂ) :
    densitySeries N w = (singularSeries N : ℂ) * ∑' k, densityMultiplicativeTerm N w k := by
  unfold densitySeries
  simp_rw [densitySeries_term_factorization N hN w]
  exact tsum_mul_left

end ConditionalGoldbach
