import ConditionalGoldbach.Proofs.MellinDifferentiation
import ConditionalGoldbach.Proofs.MellinConvolution
import ConditionalGoldbach.Proofs.MellinContourShift

/-! Mellin decay for smooth compact functions whose support can meet zero. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma compact_mellin_regular (f : ℝ → ℝ) (hf : Continuous f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun y => (f y : ℂ)) s ∧
    DifferentiableAt ℂ (mellin (fun y => (f y : ℂ))) s := by
  have hc : Continuous (fun y => (f y : ℂ)) := Complex.continuous_ofReal.comp hf
  have htop : (fun y => (f y : ℂ)) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop B] with y hy
    have hz : f y = 0 := by
      by_contra hn
      exact (not_lt_of_ge (hsupp hn).2) hy
    simp [hz]
  have hbot : (fun y => (f y : ℂ)) =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(0 : ℝ))) := by
    simpa using (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have hloc := (hc.locallyIntegrable (μ := volume)).locallyIntegrableOn (Ioi (0 : ℝ))
  exact ⟨mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0) hloc
      (htop.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith) hbot hs,
    mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hloc
      (htop.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith) hbot hs⟩

lemma mellinD_support_Icc {f : ℝ → ℝ} {A B : ℝ}
    (hs : Function.support f ⊆ Icc A B) : Function.support (mellinD f) ⊆ Icc A B := by
  have ht : tsupport f ⊆ Icc A B := closure_minimal hs isClosed_Icc
  intro x hx
  by_contra hout
  have hz : f x = 0 := by by_contra hn; exact hout (hs hn)
  have hdz : deriv f x = 0 := by by_contra hn; exact hout (ht (support_deriv_subset hn))
  exact hx (by simp [mellinD, hz, hdz])

lemma mellinD_transform_positive (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (s : ℂ) (hs : 0 < s.re) :
    mellin (fun u => (mellinD f u : ℂ)) s = (1 + s) * mellin (fun u => (f u : ℂ)) s := by
  let F : ℝ → ℂ := fun u => (u : ℂ) ^ (s - 1) * (f u : ℂ)
  let G : ℝ → ℂ := fun u => (u : ℂ) ^ s * ((deriv f u : ℝ) : ℂ)
  have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hdfs : Function.support (deriv f) ⊆ Icc A B :=
    support_deriv_subset.trans (closure_minimal hsupp isClosed_Icc)
  have hF : IntegrableOn F (Ioi 0) := (compact_mellin_regular f hf.continuous A B hsupp s hs).1
  have hG : IntegrableOn G (Ioi 0) := by
    have h := (compact_mellin_regular (deriv f) hdf.continuous A B hdfs (s + 1) (by simpa using hs.trans (lt_add_one s.re))).1
    simpa only [MellinConvergent, add_sub_cancel_right, smul_eq_mul, G] using h
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hFTC : (∫ u in Ioi (0 : ℝ), s * F u + G u) = 0 := by
    have hd (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
        HasDerivAt (fun u : ℝ => (u : ℂ) ^ s * (f u : ℂ)) (s * F u + G u) u := by
      have hcp := hasDerivAt_ofReal_cpow_const (ne_of_gt hu) hs0
      convert hcp.mul ((hf.differentiable (by norm_num) u).hasDerivAt.ofReal_comp) using 1
      dsimp [F, G]
      ring
    have hc : ContinuousWithinAt (fun u : ℝ => (u : ℂ) ^ s * (f u : ℂ)) (Ici 0) 0 :=
      ((Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).mul
        (Complex.continuous_ofReal.continuousAt.comp hf.continuous.continuousAt)).continuousWithinAt
    have htop : Tendsto (fun u : ℝ => (u : ℂ) ^ s * (f u : ℂ)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop B] with u hu
      have hz : f u = 0 := by
        by_contra hn
        exact (not_lt_of_ge (hsupp hn).2) hu
      simp [hz]
    have heq := integral_Ioi_of_hasDerivAt_of_tendsto hc hd ((hF.const_mul s).add hG) htop
    simpa only [ofReal_zero, zero_cpow hs0, zero_mul, sub_self] using heq
  rw [integral_add (hF.const_mul s) hG, integral_const_mul] at hFTC
  have heq : (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * (mellinD f u : ℂ)) =
      ∫ u in Ioi (0 : ℝ), F u - G u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hp : (u : ℂ) ^ (s - 1) * u = (u : ℂ) ^ s := by
      calc
        _ = (u : ℂ) ^ (s - 1) * (u : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
        _ = (u : ℂ) ^ ((s - 1) + 1) := (cpow_add _ _ hu0).symm
        _ = _ := by rw [sub_add_cancel]
    dsimp [F, G, mellinD]
    push_cast
    rw [mul_sub, ← mul_assoc, hp]
  unfold mellin
  simp only [smul_eq_mul]
  rw [heq, integral_sub hF hG]
  change (∫ u in Ioi (0 : ℝ), F u) - (∫ u in Ioi (0 : ℝ), G u) =
    (1 + s) * ∫ u in Ioi (0 : ℝ), F u
  linear_combination -hFTC

lemma compact_mellin_uniform_bound (f : ℝ → ℝ) (hf : Continuous f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc lo hi →
      ‖mellin (fun u => (f u : ℂ)) s‖ ≤ C := by
  let L : ℝ → ℝ := fun u => ‖(u : ℂ) ^ ((lo : ℂ) - 1) * (f u : ℂ)‖
  let H : ℝ → ℝ := fun u => ‖(u : ℂ) ^ ((hi : ℂ) - 1) * (f u : ℂ)‖
  have hL : IntegrableOn L (Ioi 0) := (compact_mellin_regular f hf A B hsupp lo hlo).1.norm
  have hH : IntegrableOn H (Ioi 0) := (compact_mellin_regular f hf A B hsupp hi (hlo.trans_le hlohi)).1.norm
  let C := ∫ u in Ioi (0 : ℝ), L u + H u
  have hC : 0 ≤ C := integral_nonneg (fun u => add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨C + 1, by positivity, fun s hs => ?_⟩
  apply le_trans _ (by linarith : C ≤ C + 1)
  unfold mellin
  simp only [smul_eq_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (compact_mellin_regular f hf A B hsupp s (hlo.trans_le hs.1)).1.norm (hL.add hH)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  dsimp [L, H]
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, sub_re, ofReal_re, one_re]
  by_cases hu1 : u ≤ 1
  · have hp := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hu hu1 (sub_le_sub_right hs.1 1)) (norm_nonneg (f u : ℂ))
    exact hp.trans (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hu.le _) (norm_nonneg _)))
  · have hp := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hu1) (sub_le_sub_right hs.2 1)) (norm_nonneg (f u : ℂ))
    exact hp.trans (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hu.le _) (norm_nonneg _)))

lemma mellinD_iterate_regular_Icc (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (k : ℕ) :
    ContDiff ℝ ∞ (mellinD^[k] f) ∧ Function.support (mellinD^[k] f) ⊆ Icc A B := by
  induction k with
  | zero => exact ⟨hf, hsupp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨mellinD_contDiff ih.1, mellinD_support_Icc ih.2⟩

lemma mellinD_iterate_transform_positive (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    mellin (fun u => (mellinD^[k] f u : ℂ)) s =
      (1 + s) ^ k * mellin (fun u => (f u : ℂ)) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', mellinD_transform_positive _
      (mellinD_iterate_regular_Icc f hf A B hsupp k).1 A B
      (mellinD_iterate_regular_Icc f hf A B hsupp k).2 s hs, ih, pow_succ]
    ring

lemma compact_mellin_rapid_decay (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (A B : ℝ) (hsupp : Function.support f ⊆ Icc A B)
    (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc lo hi →
      ‖mellin (fun u => (f u : ℂ)) s‖ ≤ C * (1 + |s.im|)⁻¹ ^ k := by
  obtain ⟨C₀, hC₀, hzero⟩ := compact_mellin_uniform_bound f hf.continuous A B hsupp lo hi hlo hlohi
  obtain ⟨Ck, hCk, hk⟩ := compact_mellin_uniform_bound (mellinD^[k] f)
    (mellinD_iterate_regular_Icc f hf A B hsupp k).1.continuous A B
    (mellinD_iterate_regular_Icc f hf A B hsupp k).2 lo hi hlo hlohi
  refine ⟨2 ^ k * (C₀ + Ck), by positivity, fun s hsl => ?_⟩
  have hnorm := hk s hsl
  rw [mellinD_iterate_transform_positive f hf A B hsupp k s (hlo.trans_le hsl.1), norm_mul, norm_pow] at hnorm
  have him : |s.im| ≤ ‖1 + s‖ := by simpa only [add_im, one_im, zero_add] using Complex.abs_im_le_norm (1 + s)
  have hpower : |s.im| ^ k * ‖mellin (fun u => (f u : ℂ)) s‖ ≤ Ck :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) him k) (norm_nonneg _)).trans hnorm
  have hden : 0 < (1 + |s.im|) ^ k := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hden]
  by_cases hsmall : |s.im| ≤ 1
  · have hpow : (1 + |s.im|) ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      _ ≤ C₀ * (2 : ℝ) ^ k := mul_le_mul (hzero s hsl) hpow (by positivity) hC₀.le
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) ^ k by positivity) hCk.le]
  · have hlarge : 1 < |s.im| := lt_of_not_ge hsmall
    have hpow : (1 + |s.im|) ^ k ≤ (2 * |s.im|) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc
      _ ≤ ‖mellin (fun u => (f u : ℂ)) s‖ * (2 * |s.im|) ^ k :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (2 : ℝ) ^ k * (|s.im| ^ k * ‖mellin (fun u => (f u : ℂ)) s‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ k * Ck := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

lemma compact_mellin_verticalIntegrable (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (σ : ℝ) (hσ : 0 < σ) :
    VerticalIntegrable (mellin (fun u => (f u : ℂ))) σ := by
  obtain ⟨C, _, hC⟩ := compact_mellin_rapid_decay f hf A B hsupp σ σ hσ le_rfl 2
  apply integrable_of_uniform_vertical_decay _ σ C
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (compact_mellin_regular f hf.continuous A B hsupp (line σ t)
      (by simpa [line] using hσ)).2.continuousAt.comp
    unfold line
    fun_prop
  · intro t
    simpa [line] using hC (line σ t) (by simp [line])

lemma compact_mellin_inversion (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (σ : ℝ) (hσ : 0 < σ) (u : ℝ) (hu : 0 < u) :
    (f u : ℂ) = verticalMellin σ (fun s => mellin (fun y => (f y : ℂ)) s * (u : ℂ) ^ (-s)) := by
  have h := mellinInv_mellin_eq σ (fun u => (f u : ℂ)) hu
    (compact_mellin_regular f hf.continuous A B hsupp σ hσ).1
    (compact_mellin_verticalIntegrable f hf A B hsupp σ hσ)
    (Complex.continuous_ofReal.continuousAt.comp hf.continuous.continuousAt)
  rw [← h]
  unfold mellinInv verticalMellin
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div, Complex.ofReal_inv]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => mul_comm _ _)

lemma compact_mellin_inversion_integrable (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (σ : ℝ) (hσ : 0 < σ) (u : ℝ) (hu : 0 < u) :
    Integrable (fun t : ℝ => mellin (fun y => (f y : ℂ)) (line σ t) * (u : ℂ) ^ (-line σ t)) := by
  have hpow : Continuous (fun t : ℝ => (u : ℂ) ^ (-line σ t)) := by
    apply Continuous.const_cpow
    · unfold line
      fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hu.ne')
  have hb : ∀ᵐ t : ℝ, ‖(u : ℂ) ^ (-line σ t)‖ ≤ Real.rpow u (-σ) := by
    filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp [line]
  simpa only [line, mul_comm] using
    (compact_mellin_verticalIntegrable f hf A B hsupp σ hσ).bdd_mul hpow.aestronglyMeasurable hb

lemma signedConvolution_mellin_decay (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      ‖mellin (fun y => (signedConvolution φ y : ℂ)) (line σ t)‖ ≤ C * (1 + |t|)⁻¹ ^ 6 := by
  obtain ⟨C, hC, hb⟩ := compact_mellin_rapid_decay (signedConvolution φ)
    (signedConvolution_contDiff φ hφ) (-(1 / 3)) (4 / 3)
    (signedConvolution_support φ hφ) lo hi hlo hlohi 6
  refine ⟨C, hC, fun σ hσ t => ?_⟩
  simpa [line] using hb (line σ t) (by simpa [line] using hσ)

lemma signedConvolution_mellin_inversion (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (u : ℝ) (hu : 0 < u) :
    (signedConvolution φ u : ℂ) = verticalMellin σ (fun s =>
      mellin (fun y => (signedConvolution φ y : ℂ)) s * (u : ℂ) ^ (-s)) :=
  compact_mellin_inversion (signedConvolution φ) (signedConvolution_contDiff φ hφ)
    (-(1 / 3)) (4 / 3) (signedConvolution_support φ hφ) σ hσ u hu

end ConditionalGoldbach
