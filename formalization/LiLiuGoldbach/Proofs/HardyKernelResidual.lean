import LiLiuGoldbach.Proofs.HardyReproducing
import LiLiuGoldbach.Proofs.KernelRegularity

/-! The residual estimate and fixed-contour bound obtained from exact kernel reproduction. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace LiLiuGoldbach16

lemma residual_norm_le_of_kernel_pairing {a : ℝ} (ha : a < beta) (ha0 : 0 ≤ a)
    (N : ℕ) [NeZero N] (T : HardySpace a beta →L[ℂ] HardySpace a beta)
    (s z : ℂ) (hs : s ∈ strip a beta) (hz : z ∈ strip a beta)
    (hpair : weightedKernel N s z = paperInner (T (evaluationVector z)) (evaluationVector s)) :
    ‖residual N s (conj z)‖ ≤ ‖T‖ * ‖1 + s‖ * ‖1 + z‖ /
      (8 * Real.sqrt (pointDistance a beta s * pointDistance a beta z)) := by
  have hns : 1 + s ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
    linarith [hs.1]
  have hnz : 1 + conj z ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re, Complex.conj_re] at hr
    linarith [hz.1]
  have hrecover : residual N s (conj z) = weightedKernel N s z * ((1 + s) * (1 + conj z)) := by
    rw [weightedKernel, div_mul_cancel₀ _ (mul_ne_zero hns hnz)]
  have hk : ‖weightedKernel N s z‖ ≤
      ‖T‖ * (‖(evaluationVector s : HardySpace a beta)‖ * ‖(evaluationVector z : HardySpace a beta)‖) := by
    rw [hpair, paperInner]
    calc
      _ ≤ ‖(evaluationVector s : HardySpace a beta)‖ * ‖T (evaluationVector z)‖ := norm_inner_le_norm _ _
      _ ≤ ‖(evaluationVector s : HardySpace a beta)‖ * (‖T‖ * ‖evaluationVector z‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  have hbound := hk.trans (mul_le_mul_of_nonneg_left (evaluationVector_norm_product_le ha hs hz) (norm_nonneg T))
  rw [hrecover, norm_mul, norm_mul]
  have hconj : ‖1 + conj z‖ = ‖1 + z‖ := by
    simpa only [map_add, map_one] using Complex.norm_conj (1 + z)
  rw [hconj]
  calc
    _ ≤ (‖T‖ * (1 / (8 * Real.sqrt (pointDistance a beta s * pointDistance a beta z)))) *
        (‖1 + s‖ * ‖1 + z‖) := mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = _ := by ring

lemma norm_one_add_line_upper (x t : ℝ) : ‖1 + line x t‖ ≤ 1 + |x| + |t| := by
  calc
    _ ≤ 1 + ‖line x t‖ := by simpa only [norm_one] using norm_add_le (1 : ℂ) (line x t)
    _ ≤ 1 + (|x| + |t|) := by
      apply add_le_add_right
      simpa [line, Complex.norm_real, norm_mul] using norm_add_le (x : ℂ) ((t : ℂ) * I)
    _ = _ := by ring

lemma fixed_contour_distance {N : ℕ} (hlarge : Real.exp 10 < (N : ℝ)) (t : ℝ) :
    1 / 90 ≤ pointDistance (alpha N) beta (line sigmaStar t) := by
  have hlog : (10 : ℝ) < Real.log N := by simpa using Real.log_lt_log (Real.exp_pos 10) hlarge
  have hα : alpha N < 1 / 10 := one_div_lt_one_div_of_lt (by norm_num) hlog
  unfold pointDistance
  simp only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  apply le_min <;> dsimp [sigmaStar, beta] <;> linarith

lemma fixed_contour_mem_strip {N : ℕ} (hlarge : Real.exp 10 < (N : ℝ)) (t : ℝ) :
    line sigmaStar t ∈ strip (alpha N) beta := by
  have hd := fixed_contour_distance hlarge t
  unfold pointDistance at hd
  have hh := le_min_iff.mp hd
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma residual_fixed_contour_bound_of_pairing (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (ha : alpha N < beta)
    (T : HardySpace (alpha N) beta →L[ℂ] HardySpace (alpha N) beta)
    (hpair : ∀ s z : ℂ, s ∈ strip (alpha N) beta → z ∈ strip (alpha N) beta →
      weightedKernel N s z = paperInner (T (evaluationVector z)) (evaluationVector s)) (v t : ℝ) :
    ‖residual N (line sigmaStar v) (line sigmaStar t)‖ ≤
      45 * ‖T‖ * (1 + |v| + |t|) ^ 2 := by
  have hv := fixed_contour_mem_strip hlarge v
  have ht := fixed_contour_mem_strip hlarge (-t)
  have hb := residual_norm_le_of_kernel_pairing ha (large_alpha_pos hlarge).le N T
    (line sigmaStar v) (line sigmaStar (-t)) hv ht (hpair _ _ hv ht)
  have he : conj (line sigmaStar (-t)) = line sigmaStar t := by
    apply Complex.ext <;> simp [line]
  rw [he] at hb
  have hds := fixed_contour_distance hlarge v
  have hdt := fixed_contour_distance hlarge (-t)
  have hprod : (1 / 90 : ℝ) ^ 2 ≤ pointDistance (alpha N) beta (line sigmaStar v) *
      pointDistance (alpha N) beta (line sigmaStar (-t)) := by
    simpa only [pow_two] using mul_le_mul hds hdt (by norm_num : (0 : ℝ) ≤ 1 / 90)
      (by linarith : 0 ≤ pointDistance (alpha N) beta (line sigmaStar v))
  have hsqrt := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 90)] at hsqrt
  have hnsv : ‖1 + line sigmaStar v‖ ≤ 2 * (1 + |v| + |t|) := by
    have hh := norm_one_add_line_upper sigmaStar v
    norm_num [sigmaStar] at hh
    dsimp only [sigmaStar]
    linarith [abs_nonneg v, abs_nonneg t]
  have hnst : ‖1 + line sigmaStar (-t)‖ ≤ 2 * (1 + |v| + |t|) := by
    have hh := norm_one_add_line_upper sigmaStar (-t)
    norm_num [sigmaStar, abs_neg] at hh
    dsimp only [sigmaStar]
    linarith [abs_nonneg v, abs_nonneg t]
  apply hb.trans
  apply (div_le_iff₀ (by positivity)).mpr
  have hm := mul_le_mul hnsv hnst (norm_nonneg _) (by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm (norm_nonneg T)
  have hd := mul_le_mul_of_nonneg_left hsqrt
    (by positivity : 0 ≤ 45 * ‖T‖ * (1 + |v| + |t|) ^ 2 * 8)
  nlinarith

end LiLiuGoldbach16
