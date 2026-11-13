import LiLiuGoldbach.Proofs.MellinDoubleSeries
import LiLiuGoldbach.Proofs.DensitySeries

/-! The diagonal term in Lemma 7.2, evaluated by absolute double Mellin inversion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

lemma mellin_diagonal_rescale (N n : ℕ) (hN : 0 < N) (hn : 0 < n) (s z a : ℂ) :
    a / (n : ℂ) * (((n : ℝ) / N : ℝ) : ℂ) ^ (-s) *
        (((n : ℝ) / N : ℝ) : ℂ) ^ (-z) =
      (N : ℂ) ^ (s + z) * (a / (n : ℂ) ^ (1 + (s + z))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hncp (w : ℂ) : (n : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
  have hNcp (w : ℂ) : (N : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hN0)
  rw [Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (a := (n : ℝ)) (b := (N : ℝ)) (by positivity) (by positivity),
    Complex.div_cpow_ofReal_nonneg (a := (n : ℝ)) (b := (N : ℝ)) (by positivity) (by positivity),
    Complex.ofReal_natCast, Complex.ofReal_natCast]
  simp only [cpow_neg, cpow_add _ _ hn0, cpow_add _ _ hN0, cpow_one]
  field_simp

lemma diagonal_mellin_coeff_summable (N : ℕ) (hN : 0 < N) (σ : ℝ) (hσ : 0 < σ) :
    Summable (fun k : ℕ =>
      ‖if Nat.Coprime (k + 1) N then (mangoldt (k + 1) : ℂ) ^ 2 / (k + 1 : ℕ) else 0‖ *
      Real.rpow ((k + 1 : ℕ) / (N : ℝ)) (-σ) ^ 2) := by
  have hs := diagonalSeries_summable N (w := (σ : ℂ) + σ) (by simpa using hσ)
  have hh := ((summable_nat_add_iff 1).2 hs).mul_left ‖(N : ℂ) ^ ((σ : ℂ) + σ)‖
  apply hh.congr
  intro k
  have hid := congrArg norm (mellin_diagonal_rescale N (k + 1) hN (by omega)
    (σ : ℂ) (σ : ℂ) ((mangoldt (k + 1) : ℂ) ^ 2))
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (k + 1 : ℕ) / (N : ℝ)),
    neg_re, ofReal_re, ← Real.rpow_eq_pow] at hid
  simp only [Nat.succ_pos, true_and]
  split_ifs with hk
  · simpa only [pow_two, mul_assoc] using hid.symm
  · simp

lemma diagonal_companion_term (N n : ℕ) (hN : 0 < N) (φ : ℝ → ℝ) :
    ((mangoldt n : ℂ) ^ 2 / (n : ℂ)) * (companion φ (n / N) : ℂ) ^ 2 =
      (N : ℂ)⁻¹ * ((mangoldt n : ℂ) ^ 2 * (φ (n / N) : ℂ) ^ 2) := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldt]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hu : 0 ≤ (n : ℝ) / N := by positivity
  simp only [companion, ofReal_mul, mul_pow]
  have hsqrt : (Real.sqrt ((n : ℝ) / N) : ℂ) ^ 2 = (n : ℂ) / N := by
    rw [← ofReal_pow, Real.sq_sqrt hu, ofReal_div, ofReal_natCast, ofReal_natCast]
  rw [hsqrt]
  field_simp

lemma diagonal_mellin_series (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ)
    (s z : ℂ) (hsz : 0 < (s + z).re) :
    (∑' k : ℕ,
      (if Nat.Coprime (k + 1) N then (mangoldt (k + 1) : ℂ) ^ 2 / (k + 1 : ℕ) else 0) *
        (mellinWeight φ s * (((k + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-s)) *
        (mellinWeight φ z * (((k + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-z))) =
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * diagonalSeries N (s + z) := by
  have hs : Summable (fun n : ℕ => if 0 < n ∧ Nat.Coprime n N then
      (mangoldt n : ℂ) ^ 2 / (n : ℂ) ^ (1 + (s + z)) else 0) := by
    apply Summable.of_norm
    simpa only [apply_ite norm, norm_zero] using diagonalSeries_summable N hsz
  have hdiag : diagonalSeries N (s + z) = ∑' k : ℕ,
      if Nat.Coprime (k + 1) N then
        (mangoldt (k + 1) : ℂ) ^ 2 / (k + 1 : ℕ) ^ (1 + (s + z)) else 0 := by
    unfold diagonalSeries
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.not_lt_zero, false_and, ite_false, zero_add, Nat.succ_pos, true_and]
  rw [hdiag, ← tsum_mul_left]
  apply tsum_congr
  intro k
  split_ifs with hk
  · have h := mellin_diagonal_rescale N (k + 1) hN (by omega) s z ((mangoldt (k + 1) : ℂ) ^ 2)
    calc
      _ = (((mangoldt (k + 1) : ℂ) ^ 2 / (k + 1 : ℕ)) *
          (((k + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-s) *
          (((k + 1 : ℕ) / (N : ℝ) : ℝ) : ℂ) ^ (-z)) * (mellinWeight φ s * mellinWeight φ z) := by ring
      _ = _ := by rw [h]; ring
  · simp

lemma diagonal_companion_tsum (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∑' k : ℕ,
      (if Nat.Coprime (k + 1) N then (mangoldt (k + 1) : ℂ) ^ 2 / (k + 1 : ℕ) else 0) *
        (companion φ ((k + 1 : ℕ) / N) : ℂ) ^ 2) = (diagonalMoment N φ : ℂ) := by
  let f : ℕ → ℂ := fun n => if Nat.Coprime n N then
    (mangoldt n : ℂ) ^ 2 * (φ (n / N) : ℂ) ^ 2 else 0
  have hfzero : ∀ n ∉ Finset.range (N + 1), f n = 0 := by
    intro n hn
    have hnlarge : N < n := by
      have h : N + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      omega
    have hz : φ ((n : ℝ) / N) = 0 := by
      by_contra hnonzero
      have hs := hφ.mem_support_interval hnonzero
      have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
      have hnr : (N : ℝ) < n := by exact_mod_cast hnlarge
      have hi := (div_le_iff₀ hNr).1 hs.2
      nlinarith
    simp [f, hz]
  have hfs : Summable f := summable_of_ne_finset_zero hfzero
  have hterm (k : ℕ) :
      (if Nat.Coprime (k + 1) N then (mangoldt (k + 1) : ℂ) ^ 2 / (k + 1 : ℕ) else 0) *
        (companion φ ((k + 1 : ℕ) / N) : ℂ) ^ 2 = (N : ℂ)⁻¹ * f (k + 1) := by
    dsimp [f]
    split_ifs with hk
    · exact diagonal_companion_term N (k + 1) hN φ
    · simp
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hzero : f 0 = 0 := by simp [f, mangoldt]
  have hsum : (∑' k, f (k + 1)) = ∑ n ∈ Finset.range (N + 1), f n := by
    rw [← zero_add (∑' k, f (k + 1)), ← hzero, ← hfs.tsum_eq_zero_add]
    exact tsum_eq_sum hfzero
  rw [hsum]
  unfold diagonalMoment
  push_cast
  simp only [f, apply_ite Complex.ofReal, ofReal_mul, ofReal_pow, ofReal_zero]

theorem diagonalMoment_mellin (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        diagonalSeries N (line σ p.1 + line σ p.2)) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * diagonalSeries N (s + z))) =
        diagonalMoment N φ := by
  obtain ⟨hi, hs⟩ := double_mellin_inversion_series φ hφ σ
    (fun k : ℕ => (k + 1 : ℕ) / (N : ℝ))
    (fun k : ℕ => if Nat.Coprime (k + 1) N then
      (mangoldt (k + 1) : ℂ) ^ 2 / (k + 1 : ℕ) else 0)
    (fun k => by positivity) (diagonal_mellin_coeff_summable N hN σ hσ)
  have hline (x y : ℝ) : 0 < (line σ x + line σ y).re := by simp [line]; linarith
  constructor
  · apply hi.congr
    filter_upwards [] with p
    exact diagonal_mellin_series N hN φ (line σ p.1) (line σ p.2) (hline _ _)
  · rw [← diagonal_companion_tsum N hN φ hφ, hs.tsum_eq]
    unfold verticalMellin
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    exact (diagonal_mellin_series N hN φ (line σ t) (line σ y) (hline _ _)).symm

end LiLiuGoldbach16
