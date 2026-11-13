import LiLiuGoldbach.Proofs.HardyConverse

/-! Exact traces for holomorphic strip functions with a common integrable square majorant. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace LiLiuGoldbach16

lemma continuous_closedStrip_line {a b : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f {s : ℂ | s.re ∈ Icc a b}) (x : Icc a b) :
    Continuous (fun t : ℝ => f (line x t)) := by
  apply hf.comp_continuous (by unfold line; fun_prop)
  intro t
  simpa only [Set.mem_ofPred_eq, line, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero] using x.property

lemma closedStrip_line_memLp_of_majorant {a b : ℝ} {f : ℂ → ℂ} {M : ℝ → ℝ}
    (hf : ContinuousOn f {s : ℂ | s.re ∈ Icc a b}) (hM : Integrable M)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ^ 2 ≤ M t) (x : Icc a b) :
    MemLp (fun t : ℝ => f (line x t)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_closedStrip_line hf x).aestronglyMeasurable).mpr
  apply hM.mono' ((continuous_closedStrip_line hf x).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using hbound x x.property t

lemma closedStrip_toLp_continuous {a b : ℝ} {f : ℂ → ℂ} {M : ℝ → ℝ}
    (hf : ContinuousOn f {s : ℂ | s.re ∈ Icc a b}) (hM : Integrable M)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ^ 2 ≤ M t) :
    Continuous (fun x : Icc a b => (closedStrip_line_memLp_of_majorant hf hM hbound x).toLp _) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hdct : Tendsto (fun x : Icc a b => ∫ t : ℝ, ‖f (line x t) - f (line y t)‖ ^ 2)
      (𝓝 y) (𝓝 0) := by
    convert tendsto_integral_filter_of_dominated_convergence (l := 𝓝 y) (fun t : ℝ => 4 * M t)
      (F := fun x : Icc a b => fun t : ℝ => ‖f (line x t) - f (line y t)‖ ^ 2)
      (f := fun _ : ℝ => (0 : ℝ)) ?_ ?_ (hM.const_mul 4) ?_ using 1 <;> try simp only [integral_zero]
    · exact Eventually.of_forall (fun x =>
        ((continuous_closedStrip_line hf x).sub (continuous_closedStrip_line hf y)).norm.pow 2 |>.aestronglyMeasurable)
    · apply Eventually.of_forall
      intro x
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn := norm_sub_le (f (line x t)) (f (line y t))
      have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      nlinarith [hbound x x.property t, hbound y y.property t,
        sq_nonneg (‖f (line x t)‖ - ‖f (line y t)‖)]
    · apply Eventually.of_forall
      intro t
      have hc : Continuous (fun x : Icc a b => f (line x t)) := by
        apply hf.comp_continuous (by unfold line; fun_prop)
        intro x
        simpa only [Set.mem_ofPred_eq, line, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          zero_mul, sub_zero, add_zero] using x.property
      have hct : Continuous (fun x : Icc a b => ‖f (line x t) - f (line y t)‖ ^ 2) :=
        (hc.sub continuous_const).norm.pow 2
      simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hct.tendsto y
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hdct
  simp only [Real.sqrt_zero] at hs
  convert hs using 1
  funext x
  let fx := (closedStrip_line_memLp_of_majorant hf hM hbound x).toLp (fun t : ℝ => f (line x t))
  let fy := (closedStrip_line_memLp_of_majorant hf hM hbound y).toLp (fun t : ℝ => f (line y t))
  have he : ‖fx - fy‖ ^ 2 = ∫ t : ℝ, ‖f (line x t) - f (line y t)‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub fx fy,
      (closedStrip_line_memLp_of_majorant hf hM hbound x).coeFn_toLp,
      (closedStrip_line_memLp_of_majorant hf hM hbound y).coeFn_toLp] with t ht hx hy
    simp only [ht, Pi.sub_apply, fx, fy, hx, hy]
  change ‖fx - fy‖ = Real.sqrt (∫ t : ℝ, ‖f (line x t) - f (line y t)‖ ^ 2)
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

lemma rawHardy_of_closedStrip_majorant {a b : ℝ} (hab : a < b) {f : ℂ → ℂ} {M : ℝ → ℝ}
    (hhol : DifferentiableOn ℂ f (strip a b))
    (hc : ContinuousOn f {s : ℂ | s.re ∈ Icc a b}) (hM : Integrable M)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ^ 2 ≤ M t) : IsRawHardy a b f := by
  refine ⟨hhol, ⟨2 * ∫ t : ℝ, M t, ?_⟩⟩
  intro ε hε hε'
  have hl : a + ε ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hr : b - ε ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hil := (closedStrip_line_memLp_of_majorant hc hM hbound ⟨a + ε, hl⟩).norm.integrable_sq
  have hir := (closedStrip_line_memLp_of_majorant hc hM hbound ⟨b - ε, hr⟩).norm.integrable_sq
  refine ⟨hil.add hir, ?_⟩
  rw [integral_add hil hir]
  have hleft := integral_mono hil hM (hbound (a + ε) hl)
  have hright := integral_mono hir hM (hbound (b - ε) hr)
  linarith

lemma hardy_representation_exact_boundary {a b : ℝ} (hab : a < b) {f : ℂ → ℂ} {M : ℝ → ℝ}
    (hc : ContinuousOn f {s : ℂ | s.re ∈ Icc a b}) (hM : Integrable M)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ^ 2 ≤ M t)
    (ψ : HardySpace a b) (hψ : ∀ s ∈ strip a b, fourierLaplace ψ s = f s) :
    ((boundaryTraces hab ψ).1 =ᵐ[volume] fun t => f (line a t)) ∧
    ((boundaryTraces hab ψ).2 =ᵐ[volume] fun t => f (line b t)) := by
  let F := fun x : Icc a b => (closedStrip_line_memLp_of_majorant hc hM hbound x).toLp _
  have hF : Continuous F := closedStrip_toLp_continuous hc hM hbound
  have hi : ∀ x : Ioo a b, interiorLine hab ψ x x.property =
      F ⟨x, ⟨x.property.1.le, x.property.2.le⟩⟩ := by
    intro x
    apply Lp.ext
    filter_upwards [(interiorLine_memLp hab x.property ψ).coeFn_toLp,
      (closedStrip_line_memLp_of_majorant hc hM hbound ⟨x, ⟨x.property.1.le, x.property.2.le⟩⟩).coeFn_toLp]
      with t ht ht'
    change ((interiorLine_memLp hab x.property ψ).toLp _) t = _
    rw [ht]
    change fourierLaplace ψ (line x t) =
      ((closedStrip_line_memLp_of_majorant hc hM hbound ⟨x, ⟨x.property.1.le, x.property.2.le⟩⟩).toLp _) t
    rw [ht']
    apply hψ
    simpa only [strip, Set.mem_ofPred_eq, line, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero, Set.mem_Ioo] using x.property
  have he : boundaryTraces hab ψ = (F ⟨a, ⟨le_rfl, hab.le⟩⟩, F ⟨b, ⟨hab.le, le_rfl⟩⟩) := by
    apply boundaryTraces_unique hab ψ _ _ (boundaryTraces_spec hab ψ)
    constructor
    · have ht : Tendsto (fun x : Ioo a b => (⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩ : Icc a b))
          (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 ⟨a, ⟨le_rfl, hab.le⟩⟩) := by
        rw [tendsto_subtype_rng]
        exact tendsto_comap.mono_right nhdsWithin_le_nhds
      simpa only [Function.comp_def, ← hi] using (hF.tendsto ⟨a, ⟨le_rfl, hab.le⟩⟩).comp ht
    · have ht : Tendsto (fun x : Ioo a b => (⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩ : Icc a b))
          (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 ⟨b, ⟨hab.le, le_rfl⟩⟩) := by
        rw [tendsto_subtype_rng]
        exact tendsto_comap.mono_right nhdsWithin_le_nhds
      simpa only [Function.comp_def, ← hi] using (hF.tendsto ⟨b, ⟨hab.le, le_rfl⟩⟩).comp ht
  rw [he]
  exact ⟨(closedStrip_line_memLp_of_majorant hc hM hbound ⟨a, ⟨le_rfl, hab.le⟩⟩).coeFn_toLp,
    (closedStrip_line_memLp_of_majorant hc hM hbound ⟨b, ⟨hab.le, le_rfl⟩⟩).coeFn_toLp⟩

lemma hardy_column_of_closedStrip_majorant {a b : ℝ} (hab : a < b) {f : ℂ → ℂ} {M : ℝ → ℝ}
    (hhol : DifferentiableOn ℂ f (strip a b))
    (hc : ContinuousOn f {s : ℂ | s.re ∈ Icc a b}) (hM : Integrable M)
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (line x t)‖ ^ 2 ≤ M t) :
    ∃ ψ : HardySpace a b, (∀ s ∈ strip a b, fourierLaplace ψ s = f s) ∧
      ((boundaryTraces hab ψ).1 =ᵐ[volume] fun t => f (line a t)) ∧
      ((boundaryTraces hab ψ).2 =ᵐ[volume] fun t => f (line b t)) := by
  obtain ⟨ψ, hψ⟩ := rawHardy_fourierLaplace_exists hab
    (rawHardy_of_closedStrip_majorant hab hhol hc hM hbound)
  exact ⟨ψ, hψ, hardy_representation_exact_boundary hab hc hM hbound ψ hψ⟩

end LiLiuGoldbach16
