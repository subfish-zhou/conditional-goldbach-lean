import ConditionalGoldbach.Proofs.CharacterZeroLocalBounds

/-! Summability of the zero measures obtained from the proved local counts. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach

lemma summable_int_one_add_abs_rpow (a : ℝ) (ha : 1 < a) :
    Summable (fun k : ℤ => (1+|(k : ℝ)|)^(-a)) := by
  have hn := (Real.summable_one_div_nat_add_rpow 1 a).mpr ha
  have hn' : Summable (fun n : ℕ => (1+(n : ℝ))^(-a)) := by
    apply hn.congr
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+1),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1+(n : ℝ)), one_div, add_comm]
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa using hn'
  · simpa using hn'

lemma summable_logarithmic_zero_majorant (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun k : ℤ => Real.log ((d : ℝ)*(|(k : ℝ)|+2)) / (1+|(k : ℝ)|)^2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs := (summable_int_one_add_abs_rpow (3/2) (by norm_num)).mul_left (2*(2*(d : ℝ))^(1/2 : ℝ))
  apply hs.of_nonneg_of_le
  · intro k
    apply div_nonneg (Real.log_nonneg _) (sq_nonneg _)
    nlinarith [abs_nonneg (k : ℝ)]
  intro k
  let x : ℝ := 1+|(k : ℝ)|
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : Real.log ((d : ℝ)*(|(k : ℝ)|+2)) ≤ 2*(2*(d : ℝ))^(1/2 : ℝ)*x^(1/2 : ℝ) := by
    have hh := Real.log_le_rpow_div (by positivity : 0 ≤ (d : ℝ)*(|(k : ℝ)|+2)) (by norm_num : (0 : ℝ)<1/2)
    have hb : (d : ℝ)*(|(k : ℝ)|+2) ≤ (2*(d : ℝ))*x := by dsimp [x]; nlinarith [abs_nonneg (k : ℝ)]
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (d : ℝ)*(|(k : ℝ)|+2)) hb (by norm_num : (0 : ℝ)≤1/2)
    rw [Real.mul_rpow (by positivity) hx.le] at hp
    linarith
  change Real.log ((d : ℝ)*(|(k : ℝ)|+2))/x^2 ≤ 2*(2*(d : ℝ))^(1/2 : ℝ)*x^(-(3/2 : ℝ))
  apply (div_le_div_of_nonneg_right hlog (sq_nonneg x)).trans_eq
  rw [mul_div_assoc, ← Real.rpow_two, ← Real.rpow_sub hx]
  norm_num

lemma zeroWindow_partition {d : ℕ} [NeZero d] (χ : Character d) (p : ZeroIndex χ) :
    ∃! k : ℤ, p ∈ zeroWindow χ k := by
  refine ⟨⌊p.val.1.im⌋, ⟨Int.floor_le _,Int.lt_floor_add_one _⟩,?_⟩
  intro k hk
  exact (Int.floor_eq_iff.mpr hk).symm

lemma primitive_zero_floor_square_summable {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    Summable (fun p : ZeroIndex χ => (1+|((⌊p.val.1.im⌋ : ℤ) : ℝ)|)⁻¹^2) := by
  classical
  obtain ⟨C,hC,hcount⟩ := primitive_local_zero_count
  have hc := hcount d inferInstance χ hχ hprim
  let f : ZeroIndex χ → ℝ := fun p => (1+|((⌊p.val.1.im⌋ : ℤ) : ℝ)|)⁻¹^2
  have hf : 0 ≤ f := fun p => sq_nonneg _
  apply (summable_partition hf (zeroWindow_partition χ)).mpr
  have hfinite (k : ℤ) : (zeroWindow χ k).Finite := (hc k).1
  have hsums (k : ℤ) : (∑' p : zeroWindow χ k, f p) =
      ((zeroWindow χ k).ncard : ℝ)*(1+|(k : ℝ)|)⁻¹^2 := by
    letI := (hfinite k).fintype
    have he (p : zeroWindow χ k) : f p = (1+|(k : ℝ)|)⁻¹^2 := by
      dsimp [f]
      rw [Int.floor_eq_iff.mpr p.property]
    simp_rw [he]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 2
    exact (Nat.card_eq_fintype_card).symm
  refine ⟨fun k => by letI := (hfinite k).fintype; exact (hasSum_fintype _).summable, ?_⟩
  simp_rw [hsums]
  have hs := (summable_logarithmic_zero_majorant d (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))).mul_left C
  apply hs.of_nonneg_of_le
  · intro k; positivity
  intro k
  have hbound := mul_le_mul_of_nonneg_right (hc k).2 (sq_nonneg ((1+|(k : ℝ)|)⁻¹))
  convert hbound using 1 <;> simp only [div_eq_mul_inv, inv_pow] <;> ring

lemma primitive_zero_square_summable {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    Summable (fun p : ZeroIndex χ => 1/(1+p.val.1.im^2)) := by
  have hs := (primitive_zero_floor_square_summable χ hχ hprim).mul_left 9
  apply hs.of_nonneg_of_le
  · intro p; positivity
  intro p
  let γ : ℝ := p.val.1.im
  let k : ℝ := (⌊γ⌋ : ℤ)
  have hk : |k| ≤ |γ|+1 := by
    apply abs_le.mpr
    have hkl := Int.floor_le γ
    have hkg := Int.lt_floor_add_one γ
    dsimp [k]
    constructor <;> linarith [le_abs_self γ,neg_abs_le γ]
  have hden : (1+|k|)^2 ≤ 9*(1+γ^2) := by
    nlinarith [sq_abs γ,sq_nonneg (|γ|-1),sq_nonneg |k|,abs_nonneg k]
  change 1/(1+γ^2) ≤ 9*((1+|k|)⁻¹)^2
  rw [inv_pow, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)

lemma primitive_zero_poisson_summable {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (x t : ℝ) (hx : 0 < x) :
    Summable (fun p : ZeroIndex χ => x/(x^2+(t-p.val.1.im)^2)) := by
  let C : ℝ := (2*x^2+1+2*t^2)/x
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCx : C*x = 2*x^2+1+2*t^2 := by dsimp [C]; field_simp
  have hC2 : 2*x ≤ C := by apply (le_div_iff₀ hx).mpr; nlinarith [sq_nonneg t]
  have hs := (primitive_zero_square_summable χ hχ hprim).mul_left C
  apply hs.of_nonneg_of_le
  · intro p; positivity
  intro p
  let γ : ℝ := p.val.1.im
  change x/(x^2+(t-γ)^2) ≤ C*(1/(1+γ^2))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hγ : γ^2 ≤ 2*(t-γ)^2+2*t^2 := by nlinarith [sq_nonneg (γ-2*t)]
  have hm := mul_le_mul_of_nonneg_left hγ hx.le
  have hb := mul_nonneg (sub_nonneg.mpr hC2) (sq_nonneg (t-γ))
  nlinarith

attribute [local instance] conductorNeZero in
theorem lemma_6_4_zero_poisson_convergence (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (x t : ℝ) (hx : 0 < x) :
    Summable (fun p : ZeroIndex χ.primitiveCharacter =>
      x / (x ^ 2 + (t - p.val.1.im) ^ 2)) := by
  exact primitive_zero_poisson_summable χ.primitiveCharacter
    (primitiveCharacter_ne_one_of_ne_one χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2))
    χ.primitiveCharacter_isPrimitive x t hx

end ConditionalGoldbach
