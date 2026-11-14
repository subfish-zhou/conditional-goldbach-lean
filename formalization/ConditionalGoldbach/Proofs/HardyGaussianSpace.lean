module

public import ConditionalGoldbach.Proofs.HardyGaussianDensity

/-! Weighted square-integrability of the Gaussian Fourier density, obtained by Fatou at both ends. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma hardyGaussian_uniform_line_bound {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ x ∈ Ioo a b, (∫ t : ℝ, ‖hardyGaussian f ε 0 (line x t)‖ ^ 2) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := rawHardy_uniform_line_bound hab hf
  let B : ℝ := Real.exp (2 * (|a| + |b|) ^ 2)
  refine ⟨B * C, mul_nonneg (Real.exp_pos _).le hC, ?_⟩
  intro ε hε hε' x hx
  have hxa : |x| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le a
      have hb := abs_nonneg b
      linarith [hx.1]
    · have h := le_abs_self b
      have ha := abs_nonneg a
      linarith [hx.2]
  have hsq : x ^ 2 ≤ (|a| + |b|) ^ 2 := by
    nlinarith [sq_abs x, abs_nonneg x, abs_nonneg a, abs_nonneg b]
  have hexp : Real.exp (2 * ε * x ^ 2) ≤ B := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hε' (sq_nonneg x)
    nlinarith
  calc
    _ ≤ ∫ t : ℝ, B * ‖f (line x t)‖ ^ 2 := by
      apply integral_mono ((hardyGaussian_line_memLp hab hf hx hε.le).norm.integrable_sq)
        ((hbound x hx).1.const_mul B)
      intro t
      exact (hardyGaussian_norm_sq_le f hε.le x t).trans
        (mul_le_mul_of_nonneg_right hexp (sq_nonneg _))
    _ = B * ∫ t : ℝ, ‖f (line x t)‖ ^ 2 := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound x hx).2 (Real.exp_pos _).le

lemma hardyGaussianDensity_line_integrable {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 < ε) :
    Integrable (fun τ : ℝ => ‖hardyGaussianDensity a b f ε τ‖ ^ 2 * Real.exp (2 * x * τ)) := by
  have h := (hardyGaussianDensity_weighted_memLp hab hf hx hε).norm.integrable_sq
  convert h using 1
  funext τ
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_comm, mul_assoc, mul_left_comm]

lemma hardyGaussianDensity_uniform_weighted_bound {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun τ : ℝ => ‖hardyGaussianDensity a b f ε τ‖ ^ 2 * hardyWeight a b τ) ∧
      (∫ τ : ℝ, ‖hardyGaussianDensity a b f ε τ‖ ^ 2 * hardyWeight a b τ) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hardyGaussian_uniform_line_bound hab hf
  refine ⟨2 * C, by positivity, ?_⟩
  intro ε hε hε'
  let δ : ℕ → ℝ := fun n => (b - a) / (n + 3)
  have hδ : ∀ n, 0 < δ n ∧ δ n < (b - a) / 2 := by
    intro n
    have hn : (0 : ℝ) < n + 3 := by positivity
    have hn' : (2 : ℝ) < n + 3 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    refine ⟨div_pos (sub_pos.mpr hab) hn, ?_⟩
    exact div_lt_div_of_pos_left (sub_pos.mpr hab) (by norm_num) hn'
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop).const_div_atTop (b - a)
  have hleft : ∀ n, a + δ n ∈ Ioo a b := fun n => ⟨by linarith [(hδ n).1], by linarith [(hδ n).2]⟩
  have hright : ∀ n, b - δ n ∈ Ioo a b := fun n => ⟨by linarith [(hδ n).2], by linarith [(hδ n).1]⟩
  let F : ℕ → ℝ → ℝ := fun n τ => ‖hardyGaussianDensity a b f ε τ‖ ^ 2 *
    (Real.exp (2 * (a + δ n) * τ) + Real.exp (2 * (b - δ n) * τ))
  have hfun : ∀ n, F n = fun τ : ℝ =>
      ‖hardyGaussianDensity a b f ε τ‖ ^ 2 * Real.exp (2 * (a + δ n) * τ) +
      ‖hardyGaussianDensity a b f ε τ‖ ^ 2 * Real.exp (2 * (b - δ n) * τ) := by
    intro n
    funext τ
    exact mul_add _ _ _
  have hi : ∀ n, Integrable (F n) := by
    intro n
    rw [hfun]
    exact (hardyGaussianDensity_line_integrable hab hf (hleft n) hε).add
      (hardyGaussianDensity_line_integrable hab hf (hright n) hε)
  have hb : ∀ n, (∫ τ : ℝ, F n τ) ≤ 2 * C := by
    intro n
    rw [hfun, integral_add (hardyGaussianDensity_line_integrable hab hf (hleft n) hε)
      (hardyGaussianDensity_line_integrable hab hf (hright n) hε),
      hardyGaussianDensity_line_integral hab hf (hleft n) hε,
      hardyGaussianDensity_line_integral hab hf (hright n) hε]
    linarith [hbound ε hε hε' (a + δ n) (hleft n), hbound ε hε hε' (b - δ n) (hright n)]
  apply nonnegative_integral_bound_of_tendsto (F := F) (by positivity) hi
    (fun n τ => by dsimp [F]; positivity) hb
    (((hardyGaussianDensity_continuous hab hf hε).norm.pow 2).mul
      (hardyWeight_continuous a b)).aestronglyMeasurable
    (fun τ => mul_nonneg (sq_nonneg _) (hardyWeight_pos a b τ).le)
  intro τ
  have hc : Continuous (fun d : ℝ => ‖hardyGaussianDensity a b f ε τ‖ ^ 2 *
      (Real.exp (2 * (a + d) * τ) + Real.exp (2 * (b - d) * τ))) := by fun_prop
  simpa only [Function.comp_def, Pi.pow_apply, Pi.mul_apply, F, hardyWeight, add_zero, sub_zero] using hc.continuousAt.tendsto.comp hδlim

lemma hardyGaussianDensity_memLp {a b ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hε : 0 < ε) (hε' : ε ≤ 1) :
    MemLp (hardyGaussianDensity a b f ε) 2 (hardyMeasure a b) := by
  apply (memLp_two_iff_integrable_sq_norm (hardyGaussianDensity_continuous hab hf hε).aestronglyMeasurable).mpr
  obtain ⟨C, hC, hb⟩ := hardyGaussianDensity_uniform_weighted_bound hab hf
  change Integrable _ (volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ)))
  rw [integrable_withDensity_iff (hardyWeight_continuous a b).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (hardyWeight_pos a b _).le, smul_eq_mul, mul_comm] using
    (hb ε hε hε').1

def hardyGaussianVector {a b ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hε : 0 < ε) (hε' : ε ≤ 1) : HardySpace a b :=
  (hardyGaussianDensity_memLp hab hf hε hε').toLp _

lemma hardyGaussianVector_uniform_norm_bound {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) : ∃ C : ℝ, ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε' : ε ≤ 1,
      ‖hardyGaussianVector hab hf hε hε'‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := hardyGaussianDensity_uniform_weighted_bound hab hf
  refine ⟨Real.sqrt C, ?_⟩
  intro ε hε hε'
  have he : ‖hardyGaussianVector hab hf hε hε'‖ ^ 2 =
      ∫ τ : ℝ, ‖hardyGaussianDensity a b f ε τ‖ ^ 2 * hardyWeight a b τ := by
    rw [hardySpace_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [(volume_absolutelyContinuous_hardyMeasure a b).ae_eq
      (hardyGaussianDensity_memLp hab hf hε hε').coeFn_toLp] with τ hτ
    rw [hardyGaussianVector, hτ]
  have h := (hb ε hε hε').2
  rw [← he] at h
  exact (Real.le_sqrt (norm_nonneg _) hC).mpr h

end ConditionalGoldbach
