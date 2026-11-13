import LiLiuGoldbach.Proofs.HardyReproducing

/-! Interior-line estimates for the converse Paley–Wiener theorem. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace LiLiuGoldbach16

lemma rawHardy_line_continuous {a b : ℝ} {f : ℂ → ℂ} (hf : IsRawHardy a b f)
    {x : ℝ} (hx : x ∈ Ioo a b) : Continuous (fun t : ℝ => f (line x t)) := by
  apply hf.1.continuousOn.comp_continuous (by unfold line; fun_prop)
  intro t
  simpa only [strip, Set.mem_ofPred_eq, line, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero, Set.mem_Ioo] using hx

lemma rawHardy_line_integral_bound_of_ne_midpoint {a b C : ℝ} (hab : a < b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (strip a b))
    (hC : ∀ ε : ℝ, 0 < ε → ε < (b - a) / 2 →
      Integrable (fun t : ℝ => ‖f (line (a + ε) t)‖ ^ 2 + ‖f (line (b - ε) t)‖ ^ 2) ∧
      (∫ t : ℝ, ‖f (line (a + ε) t)‖ ^ 2 + ‖f (line (b - ε) t)‖ ^ 2) ≤ C)
    {x : ℝ} (hx : x ∈ Ioo a b) (hxm : x ≠ (a + b) / 2) :
    Integrable (fun t : ℝ => ‖f (line x t)‖ ^ 2) ∧
      (∫ t : ℝ, ‖f (line x t)‖ ^ 2) ≤ C := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖f (line x t)‖ ^ 2) volume :=
    ((rawHardy_line_continuous ⟨hf, ⟨C, hC⟩⟩ hx).norm.pow 2).aestronglyMeasurable
  by_cases hleft : x < (a + b) / 2
  · obtain ⟨hi, hb⟩ := hC (x - a) (sub_pos.mpr hx.1) (by linarith)
    have hxa : a + (x - a) = x := by ring
    rw [hxa] at hi hb
    have hil : Integrable (fun t : ℝ => ‖f (line x t)‖ ^ 2) := by
      apply hi.mono' hmeas
      filter_upwards [] with t
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖f (line x t)‖))] using
        (le_add_of_nonneg_right (sq_nonneg (‖f (line (b - (x - a)) t)‖)))
    exact ⟨hil, (integral_mono hil hi (fun t => le_add_of_nonneg_right (sq_nonneg _))).trans hb⟩
  · obtain ⟨hi, hb⟩ := hC (b - x) (sub_pos.mpr hx.2) (by
      have : (a + b) / 2 < x := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hxm)
      linarith)
    have hxb : b - (b - x) = x := by ring
    rw [hxb] at hi hb
    have hil : Integrable (fun t : ℝ => ‖f (line x t)‖ ^ 2) := by
      apply hi.mono' hmeas
      filter_upwards [] with t
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖f (line x t)‖))] using
        (le_add_of_nonneg_left (sq_nonneg (‖f (line (a + (b - x)) t)‖)))
    exact ⟨hil, (integral_mono hil hi (fun t => le_add_of_nonneg_left (sq_nonneg _))).trans hb⟩

lemma nonnegative_integral_bound_of_tendsto {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ n, Integrable (F n)) (hFpos : ∀ n t, 0 ≤ F n t)
    (hbound : ∀ n, ∫ t, F n t ≤ C) (hg : AEStronglyMeasurable g volume)
    (hgpos : ∀ t, 0 ≤ g t) (hlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (g t))) :
    Integrable g ∧ (∫ t, g t) ≤ C := by
  have hFnorm : ∀ n, eLpNorm (F n) 1 volume ≤ ENNReal.ofReal C := by
    intro n
    rw [(memLp_one_iff_integrable.mpr (hF n)).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (hFpos n _)] using ENNReal.ofReal_le_ofReal (hbound n)
  have hnorm := Lp.eLpNorm_le_of_ae_tendsto (p := 1) (Eventually.of_forall hFnorm)
    (fun n => (hF n).aestronglyMeasurable) hg (Eventually.of_forall hlim)
  have hgi : Integrable g := memLp_one_iff_integrable.mp
    (lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top)
  refine ⟨hgi, ?_⟩
  rw [(memLp_one_iff_integrable.mpr hgi).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hnorm
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (hgpos _)] at hnorm
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hnorm

lemma rawHardy_uniform_line_bound {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioo a b,
      Integrable (fun t : ℝ => ‖f (line x t)‖ ^ 2) ∧
        (∫ t : ℝ, ‖f (line x t)‖ ^ 2) ≤ C := by
  obtain ⟨C, hC⟩ := hf.2
  have hCpos : 0 ≤ C := by
    have h := (hC ((b - a) / 4) (by linarith) (by linarith)).2
    exact (integral_nonneg (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))).trans h
  refine ⟨C, hCpos, ?_⟩
  intro x hx
  by_cases hxm : x = (a + b) / 2
  · subst x
    let xseq : ℕ → ℝ := fun n => (a + b) / 2 - (b - a) / (n + 4)
    have hseq : ∀ n, xseq n ∈ Ioo a b ∧ xseq n ≠ (a + b) / 2 := by
      intro n
      have hn : (4 : ℝ) ≤ n + 4 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hnpos : (0 : ℝ) < n + 4 := by positivity
      have hepos : 0 < (b - a) / (n + 4) := div_pos (sub_pos.mpr hab) hnpos
      have hele : (b - a) / (n + 4) ≤ (b - a) / 4 :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hab.le) (by norm_num) hn
      dsimp [xseq]
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    have hseqLim : Tendsto xseq atTop (𝓝 ((a + b) / 2)) := by
      have hn : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
        tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
      simpa only [sub_zero] using tendsto_const_nhds.sub (hn.const_div_atTop (b - a))
    have hfi := fun n => rawHardy_line_integral_bound_of_ne_midpoint hab f hf.1 hC
      (hseq n).1 (hseq n).2
    apply nonnegative_integral_bound_of_tendsto (F := fun n t => ‖f (line (xseq n) t)‖ ^ 2)
      hCpos (fun n => (hfi n).1) (fun n t => sq_nonneg _) (fun n => (hfi n).2)
      ((rawHardy_line_continuous hf hx).norm.pow 2).aestronglyMeasurable (fun t => sq_nonneg _)
    intro t
    have hs : line ((a + b) / 2) t ∈ strip a b := by
      simpa only [strip, Set.mem_ofPred_eq, line, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, add_zero, Set.mem_Ioo] using hx
    have hopen : IsOpen (strip a b) := isOpen_Ioo.preimage Complex.continuous_re
    have hc : ContinuousAt f (line ((a + b) / 2) t) :=
      hf.1.continuousOn.continuousAt (hopen.mem_nhds hs)
    have hline : Tendsto (fun n => line (xseq n) t) atTop (𝓝 (line ((a + b) / 2) t)) := by
      exact (show Continuous (fun x : ℝ => line x t) by unfold line; fun_prop).continuousAt.tendsto.comp hseqLim
    exact ((hc.tendsto.comp hline).norm).pow 2
  · exact rawHardy_line_integral_bound_of_ne_midpoint hab f hf.1 hC hx hxm

lemma rawHardy_line_memLp {a b : ℝ} (hab : a < b) {f : ℂ → ℂ} (hf : IsRawHardy a b f)
    {x : ℝ} (hx : x ∈ Ioo a b) : MemLp (fun t : ℝ => f (line x t)) 2 volume := by
  obtain ⟨C, hC, hbound⟩ := rawHardy_uniform_line_bound hab hf
  exact (memLp_two_iff_integrable_sq_norm (rawHardy_line_continuous hf hx).aestronglyMeasurable).mpr
    (hbound x hx).1

end LiLiuGoldbach16
