module

public import ConditionalGoldbach.Definitions.Characters
public import ConditionalGoldbach.Definitions.Weights
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Finite character projection

This module proves the unconditional arithmetic input of Lemma 3.1.
It uses finite character orthogonality and Mathlib's explicit Chebyshev bound.
No pending analytic or spectral theorem is used.
-/

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

/-- Conjugation of a character value at a unit is evaluation at its inverse. -/
lemma character_conj_unit {N : ℕ} [NeZero N] (χ : Character N)
    {b : ZMod N} (hb : IsUnit b) : conj (χ b) = χ b⁻¹ := by
  change star (χ b) = _
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ZMod.inv_mul_of_unit b hb, map_one]

/-- Full character orthogonality, in the conjugate convention of the paper. -/
lemma full_character_orthogonality {N : ℕ} [NeZero N]
    (a b : ZMod N) (hb : IsUnit b) :
    ∑ χ : Character N, χ a * conj (χ b) =
      if a = b then (N.totient : ℂ) else 0 := by
  simp_rw [character_conj_unit _ hb]
  calc
    (∑ χ : Character N, χ a * χ b⁻¹) = ∑ χ : Character N, χ b⁻¹ * χ a := by
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by simpa only [eq_comm] using DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb a

/-- The odd-character selector is a difference of two full character sums. -/
lemma odd_character_selector {N : ℕ} [NeZero N] (a b : ZMod N) :
    (2 : ℂ) * ∑ χ ∈ oddCharacters N, χ a * conj (χ b) =
      (∑ χ : Character N, χ a * conj (χ b)) -
      ∑ χ : Character N, χ (-a) * conj (χ b) := by
  rw [oddCharacters, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  rcases χ.even_or_odd with hχ | hχ
  · have hnot : χ (-1) ≠ -1 := hχ.not_odd
    rw [ite_eq_right hnot, hχ.eval_neg]
    ring
  · have hodd : χ (-1) = -1 := hχ
    rw [ite_eq_left hodd, hχ.eval_neg]
    ring

/-- The general finite odd-character projector (original equation 2.1).
The extra evenness and size hypotheses match the audited paper interface. -/
theorem lemma_3_1_odd_orthogonality (N : ℕ) [NeZero N]
    (_hN : Even N) (_hN4 : 4 ≤ N) (n m : ℕ) :
    (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N, χ n * conj (χ m) =
      if Nat.Coprime (n * m) N then
        (if (n : ZMod N) = m then (1 : ℂ) else 0) -
          (if (n : ZMod N) = -(m : ZMod N) then 1 else 0)
      else 0 := by
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N.totient)
  by_cases hnm : Nat.Coprime (n * m) N
  · rcases Nat.coprime_mul_iff_left.mp hnm with ⟨hn, hm⟩
    rw [ite_eq_left hnm]
    have hm' : IsUnit (m : ZMod N) := (ZMod.isUnit_iff_coprime m N).2 hm
    have h := odd_character_selector (n : ZMod N) (m : ZMod N)
    rw [full_character_orthogonality _ _ hm', full_character_orthogonality _ _ hm'] at h
    have hneg : (-(n : ZMod N) = (m : ZMod N)) ↔ (n : ZMod N) = -(m : ZMod N) := neg_eq_iff_eq_neg
    simp only [hneg] at h
    calc
      (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N, χ n * conj (χ m) =
          ((2 : ℂ) * ∑ χ ∈ oddCharacters N, χ n * conj (χ m)) / N.totient := by ring
      _ = _ := by rw [h]; split_ifs <;> simp [hφ]
  · rw [ite_eq_right hnm]
    suffices (∑ χ ∈ oddCharacters N, χ n * conj (χ m)) = 0 by rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro χ _
    have hc : ¬Nat.Coprime n N ∨ ¬Nat.Coprime m N := by
      simpa only [Nat.coprime_mul_iff_left, not_and_or] using hnm
    rcases hc with hn | hm
    · have hz : χ (n : ZMod N) = 0 := MulChar.map_nonunit χ (by simpa [ZMod.isUnit_iff_coprime] using hn)
      simp [hz]
    · have hz : χ (m : ZMod N) = 0 := MulChar.map_nonunit χ (by simpa [ZMod.isUnit_iff_coprime] using hm)
      simp [hz]

/-- The weighted correlation is nonnegative before any spectral hypotheses. -/
lemma goldbach_nonneg (N : ℕ) (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    0 ≤ goldbach N φ := by
  unfold goldbach
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact mul_nonneg (mul_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)
      (hφ.2.2.1 _).1) (hφ.2.2.1 _).1
  · exact le_rfl

lemma characterMoment_nonneg (N : ℕ) [NeZero N] (φ : ℝ → ℝ) :
    0 ≤ characterMoment N φ := by
  unfold characterMoment
  positivity

lemma diagonalMoment_nonneg (N : ℕ) (φ : ℝ → ℝ) :
    0 ≤ diagonalMoment N φ := by
  unfold diagonalMoment
  positivity

/-- The arithmetic diagonal has an explicit Chebyshev bound, uniform in the weight. -/
lemma diagonalMoment_le_log (N : ℕ) (hN : 1 ≤ N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    diagonalMoment N φ ≤ (Real.log 4 + 4) * Real.log N := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hsum : (∑ n ∈ Finset.range (N + 1),
      if Nat.Coprime n N then (mangoldt n) ^ 2 * φ (n / N) ^ 2 else 0) ≤
      Real.log N * ∑ n ∈ Finset.range (N + 1), mangoldt n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hΛ : 0 ≤ mangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hΛlog : mangoldt n ≤ Real.log N := by
      by_cases hz : n = 0
      · simpa [hz, mangoldt] using hlog
      · exact ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hnN))
    have hw := hφ.2.2.1 ((n : ℝ) / N)
    have hw2 : φ ((n : ℝ) / N) ^ 2 ≤ 1 := by nlinarith
    split_ifs
    · calc
        mangoldt n ^ 2 * φ ((n : ℝ) / N) ^ 2 ≤ mangoldt n ^ 2 := by nlinarith [sq_nonneg (mangoldt n)]
        _ ≤ Real.log N * mangoldt n := by nlinarith
    · exact mul_nonneg hlog hΛ
  have hpsi : (∑ n ∈ Finset.range (N + 1), mangoldt n) = Chebyshev.psi N := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.range_succ_eq_Icc_zero]
  unfold diagonalMoment
  calc
    (N : ℝ)⁻¹ * _ ≤ (N : ℝ)⁻¹ * (Real.log N * Chebyshev.psi N) := by
      exact mul_le_mul_of_nonneg_left (by simpa [hpsi] using hsum) (inv_nonneg.mpr hNpos.le)
    _ ≤ (N : ℝ)⁻¹ * (Real.log N * ((Real.log 4 + 4) * N)) := by
      gcongr
      exact Chebyshev.psi_le_const_mul_self hNpos.le
    _ = _ := by field_simp

/-- Expanding a finite character square requires no analytic convergence argument. -/
lemma character_sum_norm_sq_complex (N : ℕ) (χ : Character N) (s : Finset ℕ) (c : ℕ → ℝ) :
    ((‖∑ n ∈ s, (c n : ℂ) * χ n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, (c n : ℂ) * c m * (χ n * conj (χ m)) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, mul_comm]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    ring

lemma characterPolynomial_norm_sq (N : ℕ) (χ : Character N) (φ : ℝ → ℝ) :
    ‖characterPolynomial χ φ‖ ^ 2 = (N : ℝ)⁻¹ *
      ‖∑ n ∈ Finset.range (N + 1), ((mangoldt n * φ (n / N) : ℝ) : ℂ) * χ n‖ ^ 2 := by
  have heq : characterPolynomial χ φ = (Real.sqrt N : ℂ)⁻¹ *
      ∑ n ∈ Finset.range (N + 1), ((mangoldt n * φ (n / N) : ℝ) : ℂ) * χ n := by
    unfold characterPolynomial
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [heq, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The character average is a finite quadratic form in the odd projector. -/
lemma odd_character_quadratic (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
        ‖∑ n ∈ s, (c n : ℂ) * χ n‖ ^ 2 =
      ∑ n ∈ s, ∑ m ∈ s, c n * c m *
        (if Nat.Coprime (n * m) N then
          (if (n : ZMod N) = m then (1 : ℝ) else 0) -
            (if (n : ZMod N) = -(m : ZMod N) then 1 else 0)
          else 0) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, Complex.ofReal_sum]
  simp_rw [character_sum_norm_sq_complex]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := oddCharacters N) (t := s)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  calc
    (∑ χ ∈ oddCharacters N, 2 / (N.totient : ℂ) *
        ((c n : ℂ) * c m * (χ n * conj (χ m)))) =
        (c n : ℂ) * c m * (2 / (N.totient : ℂ) *
          ∑ χ ∈ oddCharacters N, χ n * conj (χ m)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      rw [lemma_3_1_odd_orthogonality N hN hN4 n m]
      split_ifs <;> norm_num

/-- Below the modulus, the positive and negative residue diagonals are ordinary equalities. -/
lemma residue_diagonals {N n m : ℕ} (_hN : 0 < N)
    (hn : 0 < n) (hnN : n < N) (hm : 0 < m) (hmN : m < N) :
    ((n : ZMod N) = m ↔ n = m) ∧
    ((n : ZMod N) = -(m : ZMod N) ↔ n + m = N) := by
  constructor
  · simp only [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hnN, Nat.mod_eq_of_lt hmN]
  · rw [← add_eq_zero_iff_eq_neg, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    constructor
    · rintro ⟨k, hk⟩
      have hk0 : 0 < k := by
        by_contra h
        have hkz : k = 0 := by omega
        simp only [hkz, mul_zero] at hk
        omega
      have hk2 : k < 2 := by
        by_contra h
        have hge : 2 ≤ k := by omega
        have hmul := Nat.mul_le_mul_left N hge
        nlinarith
      have : k = 1 := by omega
      simpa [this] using hk
    · intro h
      rw [h]

/-- On coefficient support inside `(0,N)`, congruence selectors are integer diagonals. -/
lemma weighted_residue_selector (N : ℕ) (hN : 0 < N) (c : ℕ → ℝ)
    (h0 : c 0 = 0) (hNzero : c N = 0) (n m : ℕ) (hn : n ≤ N) (hm : m ≤ N) :
    c n * c m * (if Nat.Coprime (n * m) N then
      (if (n : ZMod N) = m then (1 : ℝ) else 0) -
        (if (n : ZMod N) = -(m : ZMod N) then 1 else 0) else 0) =
    c n * c m * (if Nat.Coprime (n * m) N then
      (if n = m then (1 : ℝ) else 0) - (if n + m = N then 1 else 0) else 0) := by
  by_cases hcn : c n = 0
  · simp [hcn]
  by_cases hcm : c m = 0
  · simp [hcm]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by intro hz; apply hcn; simpa [hz] using h0)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by intro hz; apply hcm; simpa [hz] using h0)
  have hnN : n < N := lt_of_le_of_ne hn (by intro h; subst n; exact hcn hNzero)
  have hmN : m < N := lt_of_le_of_ne hm (by intro h; subst m; exact hcm hNzero)
  rcases residue_diagonals hN hn0 hnN hm0 hmN with ⟨hpos, hneg⟩
  simp only [hpos, hneg]

lemma finite_projection_term (N n m : ℕ) (c : ℕ → ℝ) :
    c n * c m * (if Nat.Coprime (n * m) N then
      (if n = m then (1 : ℝ) else 0) - (if n + m = N then 1 else 0) else 0) =
    (if n = m then (if Nat.Coprime n N then c n ^ 2 else 0) else 0) -
      (if n + m = N then (if Nat.Coprime (n * m) N then c n * c m else 0) else 0) := by
  by_cases hnm : n = m
  · subst m
    by_cases hc : Nat.Coprime n N
    · simp only [Nat.coprime_mul_iff_left, and_self, ↓reduceIte]
      split_ifs <;> ring
    · simp [Nat.coprime_mul_iff_left, hc]
  · by_cases hc : Nat.Coprime (n * m) N
    · simp only [hnm, ↓reduceIte]
      split_ifs <;> ring
    · simp [hc, hnm]

lemma sum_add_diagonal (N : ℕ) (c : ℕ → ℝ) (h0 : c 0 = 0) (hNzero : c N = 0)
    (n : ℕ) (hn : n ≤ N) :
    (∑ m ∈ Finset.range (N + 1), if n + m = N then
      (if Nat.Coprime (n * m) N then c n * c m else 0) else 0) =
      if 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N then c n * c (N - n) else 0 := by
  have heq (m : ℕ) : n + m = N ↔ m = N - n := by omega
  simp_rw [heq]
  rw [Finset.sum_ite_eq']
  have hm : N - n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  rw [ite_eq_left hm]
  by_cases hn0 : n = 0
  · simp [hn0, h0]
  by_cases hnN : n = N
  · simp [hnN, h0, hNzero]
  have hnp : 0 < n := Nat.pos_of_ne_zero hn0
  have hnl : n < N := lt_of_le_of_ne hn hnN
  simp [hnp, hnl]

/-- Finite projection for arbitrary real coefficients vanishing at the endpoints. -/
lemma finite_odd_projection (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (c : ℕ → ℝ) (h0 : c 0 = 0) (hNzero : c N = 0) :
    (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
      ‖∑ n ∈ Finset.range (N + 1), (c n : ℂ) * χ n‖ ^ 2 =
    (∑ n ∈ Finset.range (N + 1), if Nat.Coprime n N then c n ^ 2 else 0) -
    ∑ n ∈ Finset.range (N + 1),
      if 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N then c n * c (N - n) else 0 := by
  rw [odd_character_quadratic N hN hN4]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  calc
    _ = ∑ m ∈ Finset.range (N + 1), c n * c m *
        (if Nat.Coprime (n * m) N then
          (if n = m then (1 : ℝ) else 0) - (if n + m = N then 1 else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact weighted_residue_selector N (by omega) c h0 hNzero n m hnN
        (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
    _ = _ := by
      simp_rw [finite_projection_term]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ite_eq_left hn,
        sum_add_diagonal N c h0 hNzero n hnN]

/-- The paper's exact arithmetic projection, with its two different normalizations. -/
lemma goldbach_eq_diagonal_sub_character (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    goldbach N φ = diagonalMoment N φ - characterMoment N φ := by
  let c : ℕ → ℝ := fun n => mangoldt n * φ ((n : ℝ) / N)
  have h0 : c 0 = 0 := by simp [c, mangoldt]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hφ1 : φ 1 = 0 := by
    by_contra h
    have hh := hφ.2.1 (show (1 : ℝ) ∈ Function.support φ from h)
    norm_num at hh
  have hNz : c N = 0 := by simp [c, hNr, hφ1]
  have hP : characterMoment N φ = (N : ℝ)⁻¹ *
      ((2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
        ‖∑ n ∈ Finset.range (N + 1), (c n : ℂ) * χ n‖ ^ 2) := by
    unfold characterMoment
    simp_rw [characterPolynomial_norm_sq]
    change 2 / (N.totient : ℝ) * (∑ χ ∈ oddCharacters N, (N : ℝ)⁻¹ *
      ‖∑ n ∈ Finset.range (N + 1), (c n : ℂ) * χ n‖ ^ 2) = _
    rw [← Finset.mul_sum]
    ring
  have hD : (N : ℝ)⁻¹ * (∑ n ∈ Finset.range (N + 1),
      if Nat.Coprime n N then c n ^ 2 else 0) = diagonalMoment N φ := by
    unfold diagonalMoment
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp [c, mul_pow]
  have hG : (N : ℝ)⁻¹ * (∑ n ∈ Finset.range (N + 1),
      if 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N then c n * c (N - n) else 0) =
      goldbach N φ := by
    unfold goldbach
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · dsimp [c]
      ring
    · rfl
  have hproj : characterMoment N φ = diagonalMoment N φ - goldbach N φ := by
    rw [hP, finite_odd_projection N hN hN4 c h0 hNz, mul_sub, hD, hG]
  linarith

/-- Lemma 3.1, including all four clauses and a uniform explicit Chebyshev constant. -/
theorem lemma_3_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_ : NeZero N), Even N → 4 ≤ N →
      goldbach N φ = diagonalMoment N φ - characterMoment N φ ∧
      0 ≤ characterMoment N φ ∧ characterMoment N φ ≤ diagonalMoment N φ ∧
      diagonalMoment N φ ≤ C * Real.log N := by
  refine ⟨Real.log 4 + 4, by positivity, ?_⟩
  intro N hNZ hN hN4
  have hproj := goldbach_eq_diagonal_sub_character N hN hN4 φ hφ
  refine ⟨hproj, characterMoment_nonneg N φ, ?_, diagonalMoment_le_log N (by omega) φ hφ⟩
  have hnonneg := goldbach_nonneg N φ hφ
  linarith

end ConditionalGoldbach
