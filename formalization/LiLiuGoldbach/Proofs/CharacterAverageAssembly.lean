import LiLiuGoldbach.Proofs.PoissonWeightedEnergy
import LiLiuGoldbach.Proofs.CharacterPoissonAnchor

/-! The final uniform mean-square estimate, with its two analytic inputs exposed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16
attribute [local instance] conductorNeZero

lemma zeroPoisson_nonneg {N : ℕ} [NeZero N] (χ : Character N) (x t : ℝ) (hx : 0 ≤ x) :
    0 ≤ zeroPoisson χ x t := tsum_nonneg (fun p => div_nonneg hx (by positivity))

lemma zeroPoisson_width_comparison {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1)
    {σ r : ℝ} (hσ : 0 < σ) (hσr : σ ≤ r) (t : ℝ) :
    zeroPoisson χ σ t ≤ (r/σ)*zeroPoisson χ r t := by
  have hr : 0 < r := hσ.trans_le hσr
  have hnon := primitiveCharacter_ne_one_of_ne_one χ hχ
  have hi := primitive_zero_poisson_summable χ.primitiveCharacter hnon χ.primitiveCharacter_isPrimitive σ t hσ
  have hj := primitive_zero_poisson_summable χ.primitiveCharacter hnon χ.primitiveCharacter_isPrimitive r t hr
  unfold zeroPoisson
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hi (hj.mul_left _)
  intro p
  have hdσ : 0 < σ^2+(t-p.val.1.im)^2 := by positivity
  have hdr : 0 < r^2+(t-p.val.1.im)^2 := by positivity
  rw [← mul_div_assoc, div_mul_eq_mul_div, div_div]
  apply (div_le_div_iff₀ hdσ (mul_pos hσ hdr)).mpr
  have hs : σ^2 ≤ r^2 := (sq_le_sq₀ hσ.le hr.le).mpr hσr
  have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg (t-p.val.1.im))
  nlinarith

lemma realPart_le_from_zeroPoisson {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1)
    {σ r C E : ℝ} (hσ : 0 < σ) (hσr : σ ≤ r) (hC : 0 ≤ C) (hE : 0 ≤ E) (t : ℝ)
    (hcσ : |zeroPoisson χ σ t - (logDerivative χ (line σ t)).re| ≤ C*E)
    (hcr : |zeroPoisson χ r t - (logDerivative χ (line r t)).re| ≤ C*E) :
    |(logDerivative χ (line σ t)).re| ≤ (r/σ)*(‖logDerivative χ (line r t)‖+2*C*E) := by
  have hQ := zeroPoisson_width_comparison χ hχ hσ hσr t
  have hQnon := zeroPoisson_nonneg χ σ t hσ.le
  have hK : 1 ≤ r/σ := (one_le_div hσ).mpr hσr
  have hK0 : 0 ≤ r/σ := by linarith
  have hQr : zeroPoisson χ r t ≤ ‖logDerivative χ (line r t)‖+C*E := by
    have h := (abs_le.mp hcr).2
    have hn := Complex.re_le_norm (logDerivative χ (line r t))
    linarith
  calc
    _ = |zeroPoisson χ σ t - (zeroPoisson χ σ t - (logDerivative χ (line σ t)).re)| := by congr 1; ring
    _ ≤ |zeroPoisson χ σ t|+|zeroPoisson χ σ t - (logDerivative χ (line σ t)).re| := abs_sub _ _
    _ ≤ zeroPoisson χ σ t+C*E := by rw [abs_of_nonneg hQnon]; exact add_le_add le_rfl hcσ
    _ ≤ (r/σ)*(‖logDerivative χ (line r t)‖+C*E)+C*E :=
      add_le_add (hQ.trans (mul_le_mul_of_nonneg_left hQr hK0)) le_rfl
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hK (mul_nonneg hC hE)]

lemma logDerivative_energy_left_comparison (N : ℕ) [NeZero N] (hN4 : 4 ≤ N) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (σ r C : ℝ)
    (hσ : 0 < σ) (hσr : σ ≤ r) (hC : 0 ≤ C)
    (hlogi : Integrable (fun t : ℝ => Real.log ((N : ℝ)*(|t|+2)) ^ 2 / (1+t^2)))
    (hcσ : ∀ t : ℝ, |zeroPoisson χ σ t - (logDerivative χ (line σ t)).re| ≤ C*Real.log ((N : ℝ)*(|t|+2)))
    (hcr : ∀ t : ℝ, |zeroPoisson χ r t - (logDerivative χ (line r t)).re| ≤ C*Real.log ((N : ℝ)*(|t|+2))) :
    (∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1+t^2)) ≤
      4*(r/σ)^2*(∫ t : ℝ, ‖logDerivative χ (line r t)‖ ^ 2 / (1+t^2)) +
      16*(r/σ)^2*C^2*(∫ t : ℝ, Real.log ((N : ℝ)*(|t|+2))^2/(1+t^2)) +
      Real.pi*(3*(Real.log 4+4))^2 := by
  have hr := hσ.trans_le hσr
  have hχ1 := odd_character_ne_one χ (Finset.mem_filter.mp hχ).2
  have hbase := logDerivative_weighted_realPart_bound N hN4 hGRH χ hχ σ hσ
  have hri := logDerivative_weighted_square_integrable N hN4 hGRH χ hχ r hr
  have hp (t : ℝ) : (logDerivative χ (line σ t)).re^2/(1+t^2) ≤
      2*(r/σ)^2*(‖logDerivative χ (line r t)‖^2/(1+t^2)) +
      8*(r/σ)^2*C^2*(Real.log ((N : ℝ)*(|t|+2))^2/(1+t^2)) := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have he : 0 ≤ Real.log ((N : ℝ)*(|t|+2)) := Real.log_nonneg (by nlinarith [abs_nonneg t])
    have hh := realPart_le_from_zeroPoisson χ hχ1 hσ hσr hC he t (hcσ t) (hcr t)
    have hs := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
    rw [sq_abs] at hs
    have hm := mul_nonneg (sq_nonneg (r/σ)) (sq_nonneg
      (‖logDerivative χ (line r t)‖-2*C*Real.log ((N : ℝ)*(|t|+2))))
    have hb : (logDerivative χ (line σ t)).re^2 ≤
        2*(r/σ)^2*‖logDerivative χ (line r t)‖^2+
        8*(r/σ)^2*C^2*Real.log ((N : ℝ)*(|t|+2))^2 := by nlinarith
    convert div_le_div_of_nonneg_right hb (by positivity : 0 ≤ 1+t^2) using 1 <;> ring
  have hi := integral_mono hbase.1
    ((hri.const_mul (2*(r/σ)^2)).add (hlogi.const_mul (8*(r/σ)^2*C^2))) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (hri.const_mul _) (hlogi.const_mul _)] at hi
  simp only [integral_const_mul] at hi
  linarith [hbase.2]

lemma averagedLogDerivative_left_comparison (N : ℕ) [NeZero N] (hN : Even N)
    (hN4 : 4 ≤ N) (hGRH : GRH N) (σ r C : ℝ) (hσ : 0 < σ) (hσr : σ ≤ r) (hC : 0 ≤ C)
    (hlogi : Integrable (fun t : ℝ => Real.log ((N : ℝ)*(|t|+2)) ^ 2 / (1+t^2)))
    (hcσ : ∀ χ ∈ oddCharacters N, ∀ t : ℝ,
      |zeroPoisson χ σ t - (logDerivative χ (line σ t)).re| ≤ C*Real.log ((N : ℝ)*(|t|+2)))
    (hcr : ∀ χ ∈ oddCharacters N, ∀ t : ℝ,
      |zeroPoisson χ r t - (logDerivative χ (line r t)).re| ≤ C*Real.log ((N : ℝ)*(|t|+2))) :
    averagedLogDerivative N σ ≤ 4*(r/σ)^2*averagedLogDerivative N r +
      16*(r/σ)^2*C^2*(∫ t : ℝ, Real.log ((N : ℝ)*(|t|+2))^2/(1+t^2)) +
      Real.pi*(3*(Real.log 4+4))^2 := by
  unfold averagedLogDerivative
  calc
    _ ≤ (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
        (4*(r/σ)^2*(∫ t : ℝ, ‖logDerivative χ (line r t)‖^2/(1+t^2)) +
        16*(r/σ)^2*C^2*(∫ t : ℝ, Real.log ((N : ℝ)*(|t|+2))^2/(1+t^2)) +
        Real.pi*(3*(Real.log 4+4))^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ hχ =>
        logDerivative_energy_left_comparison N hN4 hGRH χ hχ σ r C hσ hσr hC hlogi (hcσ χ hχ) (hcr χ hχ))) (by positivity)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hm := odd_character_average_mass N hN hN4
      linear_combination (16*(r/σ)^2*C^2*(∫ t : ℝ, Real.log ((N : ℝ)*(|t|+2))^2/(1+t^2))+
        Real.pi*(3*(Real.log 4+4))^2) * hm

lemma lemma_6_4_of_reference_and_comparison
    (href : ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
      Real.exp 10 < (N : ℝ) → GRH N →
        averagedLogDerivative N (2 / Real.log N) ≤ A * Real.log N ^ 2)
    (hcompare : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N →
      Real.exp 10 < (N : ℝ) → GRH N → ∀ χ ∈ oddCharacters N,
      ∀ x : ℝ, 0 < x → x ≤ 1/5 → ∀ t : ℝ,
        |zeroPoisson χ x t - (logDerivative χ (line x t)).re| ≤ C * Real.log ((N : ℝ)*(|t|+2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
      Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ σ : ℝ, 0 < σ → σ ≤ beta →
        (∀ χ ∈ oddCharacters N,
          Integrable (fun t : ℝ => ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2))) ∧
        averagedLogDerivative N σ ≤ C * (Real.log N ^ 2 + σ⁻¹ ^ 2) := by
  obtain ⟨A,hA,href⟩ := href
  obtain ⟨C,hC,hcompare⟩ := hcompare
  obtain ⟨L,hL,hlog⟩ := conductor_logarithm_energy_bound
  let B : ℝ := Real.pi*(3*(Real.log 4+4))^2
  let D : ℝ := 16*A+64*C^2*L+B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2*A+D,by positivity,?_⟩
  intro N _ hN hlarge hGRH σ hσ hσβ
  have hN4 := (large_parameters hlarge).1
  have hn : (0 : ℝ) < N := (Real.exp_pos 10).trans hlarge
  have hln : 10 < Real.log N := (Real.lt_log_iff_exp_lt hn).mpr hlarge
  let r : ℝ := 2 / Real.log N
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsmall : r ≤ 1/5 := by
    dsimp [r]
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hσsmall : σ ≤ 1/5 := hσβ.trans (by norm_num [beta])
  have hri := href N inferInstance hN hlarge hGRH
  have hnexp : Real.exp 1 ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 10)).trans hlarge.le
  obtain ⟨hli,hle⟩ := hlog N hnexp
  refine ⟨fun χ hχ => logDerivative_weighted_square_integrable N hN4 hGRH χ hχ σ hσ,?_⟩
  by_cases hσr : σ ≤ r
  · have hleft := averagedLogDerivative_left_comparison N hN hN4 hGRH σ r C hσ hσr hC.le hli
      (fun χ hχ => hcompare N inferInstance hN hlarge hGRH χ hχ σ hσ hσsmall)
      (fun χ hχ => hcompare N inferInstance hN hlarge hGRH χ hχ r hr hrsmall)
    have hprod : (r/σ)^2 * Real.log N ^ 2 = 4*σ⁻¹^2 := by
      dsimp [r]
      field_simp [(show Real.log N ≠ 0 by linarith),hσ.ne']
      ring
    have hh : averagedLogDerivative N σ ≤ (16*A+64*C^2*L)*σ⁻¹^2+B := by
      apply hleft.trans
      have h1 := mul_le_mul_of_nonneg_left hri (show 0 ≤ 4*(r/σ)^2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hle (show 0 ≤ 16*(r/σ)^2*C^2 by positivity)
      calc
        _ ≤ 4*(r/σ)^2*(A*Real.log N^2)+16*(r/σ)^2*C^2*(L*Real.log N^2)+B :=
          add_le_add (add_le_add h1 h2) le_rfl
        _ = _ := by
          calc
            _ = (4*A+16*C^2*L)*((r/σ)^2*Real.log N^2)+B := by ring
            _ = _ := by rw [hprod]; ring
    have hi1 : 1 ≤ σ⁻¹ := by
      rw [inv_eq_one_div]
      exact (one_le_div hσ).mpr (hσβ.trans (by norm_num [beta]))
    have hisq : 1 ≤ σ⁻¹^2 := by nlinarith
    have hbound : averagedLogDerivative N σ ≤ D*σ⁻¹^2 := by
      apply hh.trans
      have hb := mul_le_mul_of_nonneg_left hisq hB
      dsimp [D]
      nlinarith
    apply hbound.trans
    have hnon1 : 0 ≤ (2*A+D)*Real.log N^2 := by positivity
    have hnon2 : 0 ≤ 2*A*σ⁻¹^2 := by positivity
    nlinarith
  · have hle : 0 ≤ σ-r := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hσr))
    have hshift := averagedLogDerivative_shift N hN4 hGRH r (σ-r) hr hle
    rw [add_sub_cancel] at hshift
    have hfactor : 1+(σ-r) ≤ 2 := by
      have hb : σ ≤ 1 := hσβ.trans (by norm_num [beta])
      linarith
    have hright : averagedLogDerivative N σ ≤ 2*A*Real.log N^2 := by
      apply hshift.trans
      calc
        _ ≤ (1+(σ-r))*(A*Real.log N^2) := mul_le_mul_of_nonneg_left hri (by positivity)
        _ ≤ 2*(A*Real.log N^2) := mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ = _ := by ring
    apply hright.trans
    have hnon1 : 0 ≤ D*Real.log N^2 := by positivity
    have hnon2 : 0 ≤ (2*A+D)*σ⁻¹^2 := by positivity
    nlinarith

end LiLiuGoldbach16
