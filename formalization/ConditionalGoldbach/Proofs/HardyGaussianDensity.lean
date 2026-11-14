module

public import ConditionalGoldbach.Proofs.HardyGaussian

/-! The classical Fourier density of a Gaussian-regularized Hardy function. -/
@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma hardyGaussian_norm_sq_le (f : ℂ → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (x t : ℝ) :
    ‖hardyGaussian f ε 0 (line x t)‖ ^ 2 ≤
      Real.exp (2 * ε * x ^ 2) * ‖f (line x t)‖ ^ 2 := by
  rw [hardyGaussian_line_norm]
  simp only [zero_mul, sub_zero, mul_pow]
  have hdecay : Real.exp (-ε * t ^ 2) ^ 2 ≤ 1 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) (sq_nonneg t)
  have he : Real.exp (ε * x ^ 2) ^ 2 = Real.exp (2 * ε * x ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  have hn := mul_le_mul_of_nonneg_left hdecay (sq_nonneg (‖f (line x t)‖))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le

lemma hardyGaussian_line_memLp {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 ≤ ε) :
    MemLp (fun t : ℝ => hardyGaussian f ε 0 (line x t)) 2 volume := by
  have hc : Continuous (fun t : ℝ => hardyGaussian f ε 0 (line x t)) :=
    (rawHardy_line_continuous hf hx).mul (by unfold line; fun_prop)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := ((rawHardy_line_memLp hab hf hx).norm.integrable_sq).const_mul
    (Real.exp (2 * ε * x ^ 2))
  apply hi.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using hardyGaussian_norm_sq_le f hε x t

def hardyGaussianDensity (a b : ℝ) (f : ℂ → ℂ) (ε τ : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    ∫ t : ℝ, hardyGaussian f ε τ (line ((a + b) / 2) t)

lemma hardyGaussian_frequency_factor (f : ℂ → ℂ) (ε τ x t : ℝ) :
    hardyGaussian f ε τ (line x t) =
      (Real.exp (-x * τ) : ℂ) *
        (Complex.exp ((-t * τ : ℝ) * Complex.I) * hardyGaussian f ε 0 (line x t)) := by
  simp only [hardyGaussian, Complex.ofReal_zero, zero_mul, sub_zero, Complex.ofReal_exp]
  have he : (ε : ℂ) * line x t ^ 2 - (τ : ℂ) * line x t =
      (-x * τ : ℝ) + ((-t * τ : ℝ) * Complex.I + (ε : ℂ) * line x t ^ 2) := by
    simp only [line, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  rw [he, Complex.exp_add, Complex.exp_add]
  ring

lemma hardyGaussianDensity_eq_fourier {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 < ε) (τ : ℝ) :
    hardyGaussianDensity a b f ε τ =
      (Real.exp (-x * τ) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
        𝓕 (fun t : ℝ => hardyGaussian f ε 0 (line x t)) (τ / (2 * Real.pi)) := by
  have hfourier : 𝓕 (fun t : ℝ => hardyGaussian f ε 0 (line x t)) (τ / (2 * Real.pi)) =
      ∫ t : ℝ, Complex.exp ((-t * τ : ℝ) * Complex.I) * hardyGaussian f ε 0 (line x t) := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [] with t
    have hphase : -2 * Real.pi * inner ℝ t (τ / (2 * Real.pi)) = -t * τ := by
      simp only [Real.inner_apply]
      field_simp
    rw [hphase, smul_eq_mul]
  rw [hfourier]
  unfold hardyGaussianDensity
  rw [hardyGaussian_vertical_integral_eq hab hf (show (a + b) / 2 ∈ Ioo a b by constructor <;> linarith)
    hx hε τ]
  calc
    _ = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * ∫ t : ℝ, (Real.exp (-x * τ) : ℂ) *
        (Complex.exp ((-t * τ : ℝ) * Complex.I) * hardyGaussian f ε 0 (line x t)) := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (hardyGaussian_frequency_factor f ε τ x)
    _ = _ := by rw [integral_const_mul]; ring

lemma hardyGaussianDensity_continuous {a b ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hε : 0 < ε) : Continuous (hardyGaussianDensity a b f ε) := by
  have hc : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  have he : hardyGaussianDensity a b f ε = fun τ =>
      (Real.exp (-((a + b) / 2) * τ) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
        𝓕 (fun t : ℝ => hardyGaussian f ε 0 (line ((a + b) / 2) t)) (τ / (2 * Real.pi)) :=
    funext (hardyGaussianDensity_eq_fourier hab hf hc hε)
  rw [he]
  exact ((by fun_prop : Continuous (fun τ : ℝ => (Real.exp (-((a + b) / 2) * τ) : ℂ))).mul_const _).mul
    ((classical_fourier_continuous (hardyGaussian_line_integrable hab hf hc hε 0)).comp (by fun_prop))

lemma hardyGaussianDensity_weighted_line {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 < ε) (τ : ℝ) :
    (Real.exp (x * τ) : ℂ) * hardyGaussianDensity a b f ε τ =
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
        𝓕 (fun t : ℝ => hardyGaussian f ε 0 (line x t)) (τ / (2 * Real.pi)) := by
  rw [hardyGaussianDensity_eq_fourier hab hf hx hε]
  have he : (Real.exp (x * τ) : ℂ) * (Real.exp (-x * τ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rw [← mul_assoc, ← mul_assoc, he, one_mul]

lemma hardyGaussianDensity_weighted_memLp {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 < ε) :
    MemLp (fun τ : ℝ => (Real.exp (x * τ) : ℂ) * hardyGaussianDensity a b f ε τ) 2 volume := by
  have hF := classical_fourier_memLp (hardyGaussian_line_integrable hab hf hx hε 0)
    (hardyGaussian_line_memLp hab hf hx hε.le)
  have hs := memLp_comp_real_mul hF (c := (2 * Real.pi)⁻¹) (by positivity)
  have hm := hs.const_mul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)
  convert hm using 1
  funext τ
  rw [hardyGaussianDensity_weighted_line hab hf hx hε]
  congr 2
  ring

lemma hardyGaussianDensity_line_integral {a b x ε : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) (hx : x ∈ Ioo a b) (hε : 0 < ε) :
    (∫ τ : ℝ, ‖hardyGaussianDensity a b f ε τ‖ ^ 2 * Real.exp (2 * x * τ)) =
      ∫ t : ℝ, ‖hardyGaussian f ε 0 (line x t)‖ ^ 2 := by
  let g : ℝ → ℂ := fun t => hardyGaussian f ε 0 (line x t)
  let c : ℝ := (2 * Real.pi)⁻¹
  let k : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)⁻¹
  calc
    _ = ∫ τ : ℝ, ‖(Real.exp (x * τ) : ℂ) * hardyGaussianDensity a b f ε τ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with τ
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_comm, mul_assoc, mul_left_comm]
    _ = ‖k‖ ^ 2 * ∫ τ : ℝ, ‖𝓕 g (c * τ)‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with τ
      rw [hardyGaussianDensity_weighted_line hab hf hx hε, norm_mul, mul_pow]
      rw [show τ / (2 * Real.pi) = c * τ by dsimp [c]; ring]
    _ = ‖k‖ ^ 2 * (|c⁻¹| * ∫ τ : ℝ, ‖𝓕 g τ‖ ^ 2) := by
      congr 1
      simpa only [smul_eq_mul] using
        (Measure.integral_comp_mul_left (fun τ : ℝ => ‖𝓕 g τ‖ ^ 2) c)
    _ = _ := by
      rw [classical_fourier_norm_sq_integral (hardyGaussian_line_integrable hab hf hx hε 0)
        (hardyGaussian_line_memLp hab hf hx hε.le)]
      dsimp [k, c, g]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), inv_inv,
        abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      field_simp

end ConditionalGoldbach
