import LiLiuGoldbach.Proofs.HardyRawLines

/-! Contour shifting with integrable horizontal slices, used for Gaussian regularizations. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace LiLiuGoldbach16

lemma integrable_exists_sequence_norm_zero {g : ℝ → ℂ} (hg : Integrable g) :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧ Tendsto (fun n => ‖g (t n)‖) atTop (𝓝 0) := by
  have he : ∀ n : ℕ, ∃ t : ℝ, n < t ∧ ‖g t‖ < 1 / (n + 1) := by
    intro n
    by_contra hn
    push_neg at hn
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hs : Ioi (n : ℝ) ⊆ {t | 1 / (n + 1 : ℝ) ≤ ‖g t‖} := fun t ht => hn t ht
    have hlt := lt_of_le_of_lt (measure_mono hs) (hg.measure_norm_ge_lt_top hpos)
    simpa only [Real.volume_Ioi, lt_self_iff_false] using hlt
  choose t ht hnorm using he
  refine ⟨t, tendsto_atTop_mono (fun n => (ht n).le) tendsto_natCast_atTop_atTop, ?_⟩
  have hlim : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).const_div_atTop 1
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hnorm n).le) hlim

lemma integrable_exists_sequence_both_ends_zero {g : ℝ → ℂ} (hg : Integrable g) :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
      Tendsto (fun n => g (t n)) atTop (𝓝 0) ∧
      Tendsto (fun n => g (-t n)) atTop (𝓝 0) := by
  have hneg : Integrable (fun t : ℝ => g (-t)) := by
    simpa only [neg_one_mul] using
      (integrable_comp_mul_left_iff g (by norm_num : (-1 : ℝ) ≠ 0)).mpr hg
  let G : ℝ → ℂ := fun t => ((‖g t‖ + ‖g (-t)‖ : ℝ) : ℂ)
  have hG : Integrable G := (hg.norm.add hneg.norm).ofReal
  obtain ⟨t, ht, hGt⟩ := integrable_exists_sequence_norm_zero hG
  have hGnorm : ∀ u, ‖G u‖ = ‖g u‖ + ‖g (-u)‖ := by
    intro u
    simp only [G, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [hGnorm] at hGt
  refine ⟨t, ht, ?_, ?_⟩
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_add_of_nonneg_right (norm_nonneg _)) hGt
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_add_of_nonneg_left (norm_nonneg _)) hGt

lemma holomorphic_vertical_integral_eq {a b x y : ℝ} (hxy : x ≤ y)
    (hx : a < x) (hy : y < b) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (strip a b))
    (hIx : Integrable (fun t : ℝ => F (line x t)))
    (hIy : Integrable (fun t : ℝ => F (line y t)))
    (hH : Integrable (fun t : ℝ => ∫ u in x..y, F (line u t))) :
    (∫ t : ℝ, F (line x t)) = ∫ t : ℝ, F (line y t) := by
  obtain ⟨t, ht, htop, hbot⟩ := integrable_exists_sequence_both_ends_zero hH
  have hrect : ∀ n, (∫ u in x..y, F (line u (-t n))) -
      (∫ u in x..y, F (line u (t n))) +
      Complex.I * (∫ v in -t n..t n, F (line y v)) -
      Complex.I * (∫ v in -t n..t n, F (line x v)) = 0 := by
    intro n
    have hd : DifferentiableOn ℂ F
        (uIcc (line x (-t n)).re (line y (t n)).re ×ℂ
          uIcc (line x (-t n)).im (line y (t n)).im) := by
      apply hF.mono
      intro z hz
      have hre : z.re ∈ Icc x y := by
        simpa only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, uIcc_of_le hxy, Set.mem_preimage]
          using hz.1
      exact ⟨hx.trans_le hre.1, hre.2.trans_lt hy⟩
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      (line x (-t n)) (line y (t n)) hd
    simpa only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add, smul_eq_mul] using h
  have hneg : Tendsto (fun n => -t n) atTop atBot := tendsto_neg_atTop_atBot.comp ht
  have hL := ((hbot.sub htop).add
    ((intervalIntegral_tendsto_integral hIy hneg ht).const_mul Complex.I)).sub
      ((intervalIntegral_tendsto_integral hIx hneg ht).const_mul Complex.I)
  have he : Complex.I * (∫ v : ℝ, F (line y v)) -
      Complex.I * (∫ v : ℝ, F (line x v)) = 0 := by
    have hzero : Tendsto (fun n => (∫ u in x..y, F (line u (-t n))) -
        (∫ u in x..y, F (line u (t n))) +
        Complex.I * (∫ v in -t n..t n, F (line y v)) -
        Complex.I * (∫ v in -t n..t n, F (line x v))) atTop (𝓝 0) := by
      simpa only [hrect] using tendsto_const_nhds (x := (0 : ℂ)) (f := atTop)
    simpa only [sub_self, zero_add] using tendsto_nhds_unique hL hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp he)).symm

end LiLiuGoldbach16
