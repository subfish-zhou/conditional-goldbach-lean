import LiLiuGoldbach.Proofs.CharacterZeroSummability

/-! A uniform logarithmic bound for the zero Poisson sum at a fixed positive width. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16

lemma shifted_zeroWindow_partition {d : ℕ} [NeZero d] (χ : Character d) (t : ℝ)
    (p : ZeroIndex χ) : ∃! k : ℤ, p ∈ zeroWindow χ (t+k) := by
  refine ⟨⌊p.val.1.im-t⌋, ?_, ?_⟩
  · constructor
    · have := Int.floor_le (p.val.1.im-t); linarith
    · have := Int.lt_floor_add_one (p.val.1.im-t); linarith
  · intro k hk
    have hh : (p.val.1.im-t) ∈ Ico (k : ℝ) (k+1) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    exact (Int.floor_eq_iff.mpr hh).symm

lemma shifted_logarithm_bound (d : ℕ) (hd : 1 ≤ d) (t : ℝ) (k : ℤ) :
    Real.log ((d : ℝ)*(|t+k|+2)) ≤
      5 * Real.log ((d : ℝ)*(|t|+2)) * (1+|(k : ℝ)|) ^ (1/2 : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let A : ℝ := (d : ℝ)*(|t|+2)
  let r : ℝ := 1+|(k : ℝ)|
  have hA : 2 ≤ A := by dsimp [A]; nlinarith [abs_nonneg t]
  have hr : 1 ≤ r := by dsimp [r]; nlinarith [abs_nonneg (k : ℝ)]
  have hA0 : 0 < A := by linarith
  have hr0 : 0 < r := by linarith
  have hlogA : (1/2 : ℝ) ≤ Real.log A := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    have hl := Real.log_le_log (by norm_num : (0 : ℝ)<2) hA
    norm_num at h2
    linarith
  have harg : (d : ℝ)*(|t+k|+2) ≤ A*r := by
    have hh := abs_add_le t (k : ℝ)
    dsimp [A,r]
    nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (k : ℝ)),
      mul_le_mul_of_nonneg_left hh (by linarith : (0 : ℝ) ≤ d),
      mul_nonneg (by linarith : (0 : ℝ) ≤ d) (mul_nonneg (abs_nonneg t) (abs_nonneg (k : ℝ)))]
  have hlogr : Real.log r ≤ 2*r^(1/2 : ℝ) := by
    convert Real.log_le_rpow_div hr0.le (by norm_num : (0 : ℝ)<1/2) using 1 <;> ring
  have hs : 1 ≤ r^(1/2 : ℝ) := Real.one_le_rpow hr (by norm_num)
  have hh := Real.log_le_log (by positivity : 0 < (d : ℝ)*(|t+k|+2)) harg
  rw [Real.log_mul hA0.ne' hr0.ne'] at hh
  change Real.log ((d : ℝ)*(|t+k|+2)) ≤ 5*Real.log A*r^(1/2 : ℝ)
  have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ Real.log A)
  have hp := mul_le_mul_of_nonneg_right hlogA (Real.rpow_nonneg hr0.le (1/2 : ℝ))
  nlinarith

lemma poisson_anchor_term_bound {d : ℕ} [NeZero d] (χ : Character d) (t : ℝ)
    (k : ℤ) (p : zeroWindow χ (t+k)) :
    (3/2 : ℝ) / ((3/2 : ℝ)^2+(t-p.val.val.1.im)^2) ≤ 14 / (1+|(k : ℝ)|)^2 := by
  let γ : ℝ := p.val.val.1.im
  have hk : |(k : ℝ)| ≤ |γ-t|+1 := by
    apply abs_le.mpr
    have hlo := p.property.1
    have hhi := p.property.2
    dsimp [γ]
    constructor <;> linarith [le_abs_self (p.val.val.1.im-t),neg_abs_le (p.val.val.1.im-t)]
  have hden : (1+|(k : ℝ)|)^2 ≤ 9*(1+(t-γ)^2) := by
    have hs : |γ-t|^2 = (t-γ)^2 := by rw [sq_abs]; ring
    nlinarith [sq_nonneg (|γ-t|-1),sq_nonneg |(k : ℝ)|,abs_nonneg (k : ℝ)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  change (3/2 : ℝ)*(1+|(k : ℝ)|)^2 ≤ 14*((3/2 : ℝ)^2+(t-γ)^2)
  nlinarith [sq_nonneg (t-γ)]

lemma primitive_poisson_anchor_bound : ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, ∀ (_ : NeZero d), ∀ χ : Character d, χ ≠ 1 → χ.IsPrimitive → ∀ t : ℝ,
      (∑' p : ZeroIndex χ, (3/2 : ℝ)/((3/2 : ℝ)^2+(t-p.val.1.im)^2)) ≤
        C * Real.log ((d : ℝ)*(|t|+2)) := by
  classical
  obtain ⟨C,hC,hcount⟩ := primitive_local_zero_count
  let w (k : ℤ) := (1+|(k : ℝ)|)^(-(3/2 : ℝ))
  have hw : Summable w := summable_int_one_add_abs_rpow (3/2) (by norm_num)
  have hwn : 0 ≤ ∑' k, w k := tsum_nonneg (fun k => Real.rpow_nonneg (by positivity) _)
  refine ⟨70*C*((∑' k, w k)+1), by positivity, ?_⟩
  intro d _ χ hχ hprim t
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let L := Real.log ((d : ℝ)*(|t|+2))
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith [abs_nonneg t])
  let q (p : ZeroIndex χ) := (3/2 : ℝ)/((3/2 : ℝ)^2+(t-p.val.1.im)^2)
  have hq : Summable q := primitive_zero_poisson_summable χ hχ hprim (3/2) t (by norm_num)
  let S (k : ℤ) := zeroWindow χ (t+k)
  have hpart := shifted_zeroWindow_partition χ t
  have hfinite (k : ℤ) : (S k).Finite := (hcount d inferInstance χ hχ hprim (t+k)).1
  have hs (k : ℤ) : (∑' p : S k, q p) ≤ 70*C*L*w k := by
    letI := (hfinite k).fintype
    have ht : (∑' p : S k, q p) ≤ ((S k).ncard : ℝ) * (14/(1+|(k : ℝ)|)^2) := by
      rw [tsum_fintype]
      calc
        _ ≤ ∑ _p : S k, 14/(1+|(k : ℝ)|)^2 :=
          Finset.sum_le_sum (fun p _ => poisson_anchor_term_bound χ t k p)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; congr 2; exact (Nat.card_eq_fintype_card).symm
    have hc := (hcount d inferInstance χ hχ hprim (t+k)).2
    have hl := shifted_logarithm_bound d hd t k
    have hcard : ((S k).ncard : ℝ) ≤ 5*C*L*(1+|(k : ℝ)|)^(1/2 : ℝ) := by
      apply hc.trans
      convert mul_le_mul_of_nonneg_left hl hC.le using 1 <;> dsimp [L]; ring
    apply ht.trans
    apply (mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 14/(1+|(k : ℝ)|)^2)).trans_eq
    dsimp [w]
    have hp : (1+|(k : ℝ)|)^(1/2 : ℝ) / (1+|(k : ℝ)|)^2 =
        (1+|(k : ℝ)|)^(-(3/2 : ℝ)) := by
      rw [← Real.rpow_two, ← Real.rpow_sub (by positivity : 0 < 1+|(k : ℝ)|)]
      norm_num
    calc
      _ = 70*C*L*((1+|(k : ℝ)|)^(1/2 : ℝ)/(1+|(k : ℝ)|)^2) := by ring
      _ = _ := by rw [hp]
  have hσ : Summable (fun p : (k : ℤ) × S k => q p.2) := (Set.sigmaEquiv S hpart).summable_iff.mpr hq
  have he : (∑' p, q p) = ∑' k, ∑' p : S k, q p := by
    rw [← (Set.sigmaEquiv S hpart).tsum_eq q]
    exact hσ.tsum_sigma' (fun k => by letI := (hfinite k).fintype; exact (hasSum_fintype _).summable)
  change (∑' p, q p) ≤ _
  rw [he]
  calc
    _ ≤ ∑' k, 70*C*L*w k :=
      Summable.tsum_le_tsum hs ((summable_partition (fun p => by dsimp [q]; positivity) hpart).mp hq).2 (hw.mul_left _)
    _ = 70*C*L*(∑' k, w k) := tsum_mul_left
    _ ≤ _ := by nlinarith [mul_nonneg hC.le hL]

attribute [local instance] conductorNeZero in
lemma zeroPoisson_anchor_bound : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∀ (_ : NeZero N), ∀ χ : Character N, χ ≠ 1 → ∀ t : ℝ,
      zeroPoisson χ (3/2) t ≤ C * Real.log ((N : ℝ)*(|t|+2)) := by
  obtain ⟨C,hC,hbound⟩ := primitive_poisson_anchor_bound
  refine ⟨C,hC,?_⟩
  intro N _ χ hχ t
  have hh := hbound χ.conductor inferInstance χ.primitiveCharacter
    (primitiveCharacter_ne_one_of_ne_one χ hχ) χ.primitiveCharacter_isPrimitive t
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hdpos : (0 : ℝ) < χ.conductor := by exact_mod_cast (NeZero.pos χ.conductor)
  apply Real.log_le_log (mul_pos hdpos (by positivity))
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level

end LiLiuGoldbach16
