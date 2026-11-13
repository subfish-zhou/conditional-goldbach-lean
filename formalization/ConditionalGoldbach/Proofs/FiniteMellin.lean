import ConditionalGoldbach.Proofs.MellinCompactPositive

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma mellinD_contDiff_finite (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ (n+1) f) :
    ContDiff ℝ n (mellinD f) := by
  have hg : ContDiff ℝ n (deriv f) := hf.deriv'
  exact (hf.of_le (by exact_mod_cast (Nat.le_succ n))).sub (contDiff_id.mul hg)

lemma mellinD_iterate_regular_finite (n k : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (n+k) f)
    (A B : ℝ) (hsupp : Function.support f ⊆ Icc A B) :
    ContDiff ℝ n (mellinD^[k] f) ∧ Function.support (mellinD^[k] f) ⊆ Icc A B := by
  induction k generalizing f with
  | zero => simpa using And.intro hf hsupp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    · apply mellinD_contDiff_finite (n+k)
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hf
    · exact mellinD_support_Icc hsupp

lemma mellinD_transform_finite (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (s : ℂ) (hs : 0 < s.re) :
    mellin (fun u => (mellinD f u : ℂ)) s = (1 + s) * mellin (fun u => (f u : ℂ)) s := by
  let F : ℝ → ℂ := fun u => (u : ℂ) ^ (s - 1) * (f u : ℂ)
  let G : ℝ → ℂ := fun u => (u : ℂ) ^ s * ((deriv f u : ℝ) : ℂ)
  have hdf : ContDiff ℝ 0 (deriv f) := hf.deriv'
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

lemma mellinD_iterate_transform_finite (k : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ k f)
    (A B : ℝ) (hsupp : Function.support f ⊆ Icc A B) (s : ℂ) (hs : 0<s.re) :
    mellin (fun u => (mellinD^[k] f u : ℂ)) s = (1+s)^k*mellin (fun u => (f u : ℂ)) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := mellinD_iterate_regular_finite 1 k f (by simpa only [Nat.cast_add,Nat.cast_one,add_comm] using hf) A B hsupp
    rw [Function.iterate_succ_apply',mellinD_transform_finite _ hk.1 A B hk.2 s hs,
      ih (hf.of_le (by exact_mod_cast Nat.le_succ k)),pow_succ]
    ring

lemma compact_mellin_finite_decay (k : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ k f)
    (A B : ℝ) (hsupp : Function.support f ⊆ Icc A B)
    (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc lo hi →
      ‖mellin (fun u => (f u : ℂ)) s‖ ≤ C * (1 + |s.im|)⁻¹ ^ k := by
  obtain ⟨C₀, hC₀, hzero⟩ := compact_mellin_uniform_bound f hf.continuous A B hsupp lo hi hlo hlohi
  obtain ⟨Ck, hCk, hk⟩ := compact_mellin_uniform_bound (mellinD^[k] f)
    (mellinD_iterate_regular_finite 0 k f (by simpa using hf) A B hsupp).1.continuous A B
    (mellinD_iterate_regular_finite 0 k f (by simpa using hf) A B hsupp).2 lo hi hlo hlohi
  refine ⟨2 ^ k * (C₀ + Ck), by positivity, fun s hsl => ?_⟩
  have hnorm := hk s hsl
  rw [mellinD_iterate_transform_finite k f hf A B hsupp s (hlo.trans_le hsl.1), norm_mul, norm_pow] at hnorm
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

lemma compact_mellin_finite_verticalIntegrable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (σ : ℝ) (hσ : 0 < σ) :
    VerticalIntegrable (mellin (fun u => (f u : ℂ))) σ := by
  obtain ⟨C, _, hC⟩ := compact_mellin_finite_decay 2 f hf A B hsupp σ σ hσ le_rfl
  apply integrable_of_uniform_vertical_decay _ σ C
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (compact_mellin_regular f hf.continuous A B hsupp (line σ t)
      (by simpa [line] using hσ)).2.continuousAt.comp
    unfold line
    fun_prop
  · intro t
    simpa [line] using hC (line σ t) (by simp [line])

lemma compact_mellin_finite_inversion (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ)
    (hsupp : Function.support f ⊆ Icc A B) (σ : ℝ) (hσ : 0 < σ) (u : ℝ) (hu : 0 < u) :
    (f u : ℂ) = verticalMellin σ (fun s => mellin (fun y => (f y : ℂ)) s * (u : ℂ) ^ (-s)) := by
  have h := mellinInv_mellin_eq σ (fun u => (f u : ℂ)) hu
    (compact_mellin_regular f hf.continuous A B hsupp σ hσ).1
    (compact_mellin_finite_verticalIntegrable f hf A B hsupp σ hσ)
    (Complex.continuous_ofReal.continuousAt.comp hf.continuous.continuousAt)
  rw [← h]
  unfold mellinInv verticalMellin
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div, Complex.ofReal_inv]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => mul_comm _ _)

lemma compact_mellin_finite_inversion_integrable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (A B : ℝ)
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
    (compact_mellin_finite_verticalIntegrable f hf A B hsupp σ hσ).bdd_mul hpow.aestronglyMeasurable hb


end ConditionalGoldbach
