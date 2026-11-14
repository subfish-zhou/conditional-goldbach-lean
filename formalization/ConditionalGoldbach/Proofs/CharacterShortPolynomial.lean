module

public import ConditionalGoldbach.Proofs.CharacterTraceBounds

/-! Exact odd-character Parseval for complex coefficients supported strictly below N/2. -/
public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma complex_character_sum_norm_sq (N : ℕ) (χ : Character N) (S : Finset ℕ) (c : ℕ → ℂ) :
    ((‖∑ n ∈ S, c n * χ n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, c n * conj (c m) * (χ n * conj (χ m)) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, mul_comm]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma odd_character_quadratic_complex (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (S : Finset ℕ) (c : ℕ → ℂ) :
    (((2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
      ‖∑ n ∈ S, c n * χ n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, c n * conj (c m) *
        (if Nat.Coprime (n * m) N then
          (if (n : ZMod N) = m then (1 : ℂ) else 0) -
            (if (n : ZMod N) = -(m : ZMod N) then 1 else 0) else 0) := by
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, Complex.ofReal_sum]
  simp_rw [complex_character_sum_norm_sq]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := oddCharacters N) (t := S)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  calc
    _ = c n * conj (c m) * ((2 : ℂ) / N.totient * ∑ χ ∈ oddCharacters N, χ n * conj (χ m)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by rw [lemma_3_1_odd_orthogonality N hN hN4]

lemma odd_character_short_parseval (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (S : Finset ℕ) (c : ℕ → ℂ)
    (hsupport : ∀ n ∈ S, c n ≠ 0 → 0 < n ∧ 2 * n < N) :
    (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N, ‖∑ n ∈ S, c n * χ n‖ ^ 2 =
      ∑ n ∈ S, if Nat.Coprime n N then ‖c n‖ ^ 2 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [odd_character_quadratic_complex N hN hN4]
  simp only [Complex.ofReal_sum, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero]
  apply Finset.sum_congr rfl
  intro n hn
  have hterm (m : ℕ) (hm : m ∈ S) : c n * conj (c m) *
      (if Nat.Coprime (n * m) N then
        (if (n : ZMod N) = m then (1 : ℂ) else 0) -
          (if (n : ZMod N) = -(m : ZMod N) then 1 else 0) else 0) =
      if m = n then (if Nat.Coprime n N then ((‖c n‖ ^ 2 : ℝ) : ℂ) else 0) else 0 := by
    by_cases hcn : c n = 0
    · simp [hcn]
    by_cases hcm : c m = 0
    · by_cases hmn : m = n
      · subst m
        exact False.elim (hcn hcm)
      · simp [hcm, hmn]
    obtain ⟨hn0, hn2⟩ := hsupport n hn hcn
    obtain ⟨hm0, hm2⟩ := hsupport m hm hcm
    obtain ⟨hpos, hneg⟩ := residue_diagonals (by omega : 0 < N) hn0 (by omega) hm0 (by omega)
    have hsum : n + m ≠ N := by omega
    simp only [hpos, hneg, hsum, ite_false, sub_zero]
    by_cases hmn : m = n
    · subst m
      simp only [ite_true, Nat.coprime_mul_iff_left, and_self]
      split_ifs <;> simp only [mul_one, mul_zero]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · simp [hmn, Ne.symm hmn]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S n]
  simp [hn]

lemma smoothedPerronWeight_eq_zero_of_le {X : ℝ} (hX : 1 < X) (n : ℕ) (hn : X ≤ (n : ℝ)) :
    smoothedPerronWeight X n = 0 := by
  have hs : Real.sqrt X < X := by
    apply (Real.sqrt_lt (by linarith : 0 ≤ X) (by linarith : 0 ≤ X)).mpr
    nlinarith
  have hn' : ¬(n : ℝ) ≤ Real.sqrt X := by linarith
  unfold smoothedPerronWeight
  rw [ite_eq_right hn']
  split_ifs with hnX
  · have he : (n : ℝ) = X := le_antisymm hnX hn
    rw [he, div_self (by linarith : X ≠ 0), Real.log_one, zero_div]
  · rfl

lemma smoothedPerronWeight_nonneg_le_one {X : ℝ} (hX : 1 < X) (n : ℕ) :
    0 ≤ smoothedPerronWeight X n ∧ smoothedPerronWeight X n ≤ 1 := by
  unfold smoothedPerronWeight
  split_ifs with hn hnX
  · exact ⟨zero_le_one, le_rfl⟩
  · have hs : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 < Real.log (Real.sqrt X) := Real.log_pos hs
    constructor
    · apply div_nonneg _ hlog.le
      exact Real.log_nonneg ((one_le_div hn0).mpr hnX)
    · apply (div_le_one hlog).mpr
      apply Real.log_le_log (div_pos (by linarith) hn0)
      apply (div_le_iff₀ hn0).mpr
      have hsq := Real.sq_sqrt (by linarith : 0 ≤ X)
      nlinarith [Real.sqrt_nonneg X]
  · exact ⟨le_rfl, zero_le_one⟩

lemma smoothed_polynomial_odd_parseval (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) (u : ℂ) :
    (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
      ‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) u‖ ^ 2 =
      ∑ n ∈ Finset.range (⌊(N : ℝ) / 2⌋₊ + 1), if Nat.Coprime n N then
        ‖(mangoldt n : ℂ) * (n : ℂ) ^ (-u) * smoothedPerronWeight ((N : ℝ) / 2) n‖ ^ 2 else 0 := by
  let S := Finset.range (⌊(N : ℝ) / 2⌋₊ + 1)
  let c : ℕ → ℂ := fun n => (mangoldt n : ℂ) * (n : ℂ) ^ (-u) * smoothedPerronWeight ((N : ℝ) / 2) n
  have hpoly (χ : Character N) : smoothedDirichletPolynomial χ ((N : ℝ) / 2) u =
      ∑ n ∈ S, c n * χ n := by
    apply Finset.sum_congr rfl
    intro n _
    dsimp [c]
    ring
  simp_rw [hpoly]
  apply odd_character_short_parseval N hN hN4 S c
  intro n hn hcn
  have h0 : c 0 = 0 := by simp [c, mangoldt]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by intro he; subst n; exact hcn h0)
  refine ⟨hn0, ?_⟩
  by_contra hnN
  have hreal : (N : ℝ) / 2 ≤ n := by
    have hh : N ≤ 2 * n := le_of_not_gt hnN
    exact (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast (show N ≤ n * 2 by omega))
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hw := smoothedPerronWeight_eq_zero_of_le (by linarith : 1 < (N : ℝ) / 2) n hreal
  apply hcn
  simp only [c, hw, Complex.ofReal_zero, mul_zero]

end ConditionalGoldbach
