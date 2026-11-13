import ConditionalGoldbach.Proofs.CharacterZeroSummability

/-! Fractional-power summability of the multiplicity-indexed zeros, for Perron--Hadamard Fubini. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Filter
namespace ConditionalGoldbach

lemma summable_logarithmic_zero_five_quarters (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun k : ℤ => Real.log ((d : ℝ) * (|(k : ℝ)| + 2)) /
      (1 + |(k : ℝ)|)^(5 / 4 : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs := (summable_int_one_add_abs_rpow (9 / 8) (by norm_num)).mul_left
    (8 * (2 * (d : ℝ))^(1 / 8 : ℝ))
  apply hs.of_nonneg_of_le
  · intro k
    apply div_nonneg (Real.log_nonneg _) (by positivity)
    nlinarith [abs_nonneg (k : ℝ)]
  intro k
  let x : ℝ := 1 + |(k : ℝ)|
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : Real.log ((d : ℝ) * (|(k : ℝ)| + 2)) ≤
      8 * (2 * (d : ℝ))^(1 / 8 : ℝ) * x^(1 / 8 : ℝ) := by
    have hh := Real.log_le_rpow_div (by positivity : 0 ≤ (d : ℝ) * (|(k : ℝ)| + 2))
      (by norm_num : (0 : ℝ) < 1 / 8)
    have hb : (d : ℝ) * (|(k : ℝ)| + 2) ≤ (2 * (d : ℝ)) * x := by
      dsimp [x]
      nlinarith [abs_nonneg (k : ℝ)]
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (d : ℝ) * (|(k : ℝ)| + 2)) hb
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [Real.mul_rpow (by positivity) hx.le] at hp
    linarith
  change Real.log ((d : ℝ) * (|(k : ℝ)| + 2)) / x^(5 / 4 : ℝ) ≤
    8 * (2 * (d : ℝ))^(1 / 8 : ℝ) * x^(-(9 / 8 : ℝ))
  apply (div_le_div_of_nonneg_right hlog (by positivity)).trans_eq
  rw [mul_div_assoc, ← Real.rpow_sub hx]
  norm_num

lemma primitive_zero_floor_five_quarters_summable {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    Summable (fun p : ZeroIndex χ =>
      (1 + |((⌊p.val.1.im⌋ : ℤ) : ℝ)|)^(-(5 / 4 : ℝ))) := by
  classical
  obtain ⟨C, hC, hcount⟩ := primitive_local_zero_count
  have hc := hcount d inferInstance χ hχ hprim
  let f : ZeroIndex χ → ℝ := fun p => (1 + |((⌊p.val.1.im⌋ : ℤ) : ℝ)|)^(-(5 / 4 : ℝ))
  have hf : 0 ≤ f := fun p => Real.rpow_nonneg (by positivity) _
  apply (summable_partition hf (zeroWindow_partition χ)).mpr
  have hfinite (k : ℤ) : (zeroWindow χ k).Finite := (hc k).1
  have hsums (k : ℤ) : (∑' p : zeroWindow χ k, f p) =
      ((zeroWindow χ k).ncard : ℝ) * (1 + |(k : ℝ)|)^(-(5 / 4 : ℝ)) := by
    letI := (hfinite k).fintype
    have he (p : zeroWindow χ k) : f p = (1 + |(k : ℝ)|)^(-(5 / 4 : ℝ)) := by
      dsimp [f]
      rw [Int.floor_eq_iff.mpr p.property]
    simp_rw [he]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 2
    exact (Nat.card_eq_fintype_card).symm
  refine ⟨fun k => by letI := (hfinite k).fintype; exact (hasSum_fintype _).summable, ?_⟩
  simp_rw [hsums]
  have hs := (summable_logarithmic_zero_five_quarters d
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))).mul_left C
  apply hs.of_nonneg_of_le
  · intro k
    positivity
  intro k
  have hb := mul_le_mul_of_nonneg_right (hc k).2
    (Real.rpow_nonneg (show 0 ≤ 1 + |(k : ℝ)| by positivity) (-(5 / 4 : ℝ)))
  convert hb using 1 <;> rw [Real.rpow_neg (by positivity), div_eq_mul_inv] <;> ring

lemma negative_rpow_comparison {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A ≤ C * B) {r : ℝ} (hr : 0 ≤ r) :
    B^(-r) ≤ C^r * A^(-r) := by
  have hh := Real.rpow_le_rpow hA.le h hr
  rw [Real.mul_rpow hC.le hB.le] at hh
  rw [Real.rpow_neg hB.le, Real.rpow_neg hA.le]
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hA _)).mpr (by simpa using hh)

lemma primitive_zero_five_quarters_summable {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    Summable (fun p : ZeroIndex χ => (1 + |p.val.1.im|)^(-(5 / 4 : ℝ))) := by
  have hs := (primitive_zero_floor_five_quarters_summable χ hχ hprim).mul_left (2^(5 / 4 : ℝ))
  apply hs.of_nonneg_of_le (fun p => Real.rpow_nonneg (by positivity) _)
  intro p
  have hk : |((⌊p.val.1.im⌋ : ℤ) : ℝ)| ≤ |p.val.1.im| + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [Int.floor_le p.val.1.im, Int.lt_floor_add_one p.val.1.im,
      le_abs_self p.val.1.im, neg_abs_le p.val.1.im]
  exact negative_rpow_comparison (by positivity) (by positivity) (by norm_num)
    (by linarith [abs_nonneg p.val.1.im] :
      1 + |((⌊p.val.1.im⌋ : ℤ) : ℝ)| ≤ 2 * (1 + |p.val.1.im|)) (by norm_num)

lemma primitive_zero_shift_five_quarters_summable {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℝ) :
    Summable (fun p : ZeroIndex χ =>
      (1 + |(t - p.val.1.im) / (2 * Real.pi)|)^(-(5 / 4 : ℝ))) := by
  let C := 1 + |t| + 2 * Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  have hs := (primitive_zero_five_quarters_summable χ hχ hprim).mul_left (C^(5 / 4 : ℝ))
  apply hs.of_nonneg_of_le (fun p => Real.rpow_nonneg (by positivity) _)
  intro p
  have hh : 1 + |p.val.1.im| ≤ C * (1 + |(t - p.val.1.im) / (2 * Real.pi)|) := by
    have he : 2 * Real.pi * |(t - p.val.1.im) / (2 * Real.pi)| = |t - p.val.1.im| := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      field_simp
    have ht := abs_sub t (t - p.val.1.im)
    rw [sub_sub_cancel] at ht
    dsimp [C]
    nlinarith [Real.pi_pos, abs_nonneg t, abs_nonneg ((t - p.val.1.im) / (2 * Real.pi)),
      mul_nonneg (abs_nonneg t) (abs_nonneg ((t - p.val.1.im) / (2 * Real.pi)))]
  exact negative_rpow_comparison (by positivity) (by positivity) hC hh (by norm_num)

end ConditionalGoldbach
