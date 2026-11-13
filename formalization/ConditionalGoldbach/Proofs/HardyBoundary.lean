import ConditionalGoldbach.Proofs.HardyInterior

/-! Construction of the endpoint Fourier–Laplace traces by L² limits. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform
open scoped Topology
namespace ConditionalGoldbach

private def realScaleMeasure (c : ℝ) : Measure ℝ := ENNReal.ofReal |c⁻¹| • volume

private lemma realScale_measurePreserving {c : ℝ} (hc : c ≠ 0) :
    MeasurePreserving (fun t : ℝ => c * t) volume (realScaleMeasure c) :=
  ⟨by fun_prop, Real.map_volume_mul_left hc⟩

private def rescaleL2 (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun t : ℝ => c * t) (realScale_measurePreserving hc)
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (show realScaleMeasure c ≤ ENNReal.ofReal |c⁻¹| • volume from le_rfl) f)

private lemma rescaleL2_continuous (c : ℝ) (hc : c ≠ 0) : Continuous (rescaleL2 c hc) :=
  (Lp.isometry_compMeasurePreserving (E := ℂ) (p := 2)
    (realScale_measurePreserving hc)).continuous.comp
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (show realScaleMeasure c ≤ ENNReal.ofReal |c⁻¹| • volume from le_rfl)).continuous

private lemma rescaleL2_coe (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    rescaleL2 c hc f =ᵐ[volume] (fun t => f (c * t)) := by
  refine (Lp.coeFn_compMeasurePreserving _ (realScale_measurePreserving hc)).trans ?_
  exact (realScale_measurePreserving hc).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (show realScaleMeasure c ≤ ENNReal.ofReal |c⁻¹| • volume from le_rfl) f)

private def physicalFourierL2 (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
    rescaleL2 (-(2 * Real.pi)⁻¹)
      (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))) (𝓕 f)

private lemma physicalFourierL2_continuous : Continuous physicalFourierL2 := by
  unfold physicalFourierL2
  exact ((rescaleL2_continuous (-(2 * Real.pi)⁻¹) _).comp
    (continuous_fourier : Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => 𝓕 f))).const_smul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)

private lemma L2_norm_sq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ t : ℝ, ‖f t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private lemma toLp_norm_eq_sqrt_integral {f : ℝ → ℂ} (hf : MemLp f 2) :
    ‖hf.toLp f‖ = Real.sqrt (∫ t : ℝ, ‖f t‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (hf.toLp f)), L2_norm_sq_integral]
  congr 1
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖ ^ 2))

private def hardyLineDensity {a b : ℝ} (ψ : HardySpace a b) (x : Icc a b) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (hardy_weighted_line_memLp x.property ψ).toLp _

private lemma hardyLineDensity_diff_bound {a b : ℝ} (ψ : HardySpace a b)
    (x y : Icc a b) (τ : ℝ) :
    ‖(Real.exp (x.val * τ) : ℂ) * ψ τ - (Real.exp (y.val * τ) : ℂ) * ψ τ‖ ^ 2 ≤
      4 * (‖ψ τ‖ ^ 2 * hardyWeight a b τ) := by
  have hx := mul_le_mul_of_nonneg_right (hardy_exp_sq_le_weight x.property τ) (sq_nonneg ‖ψ τ‖)
  have hy := mul_le_mul_of_nonneg_right (hardy_exp_sq_le_weight y.property τ) (sq_nonneg ‖ψ τ‖)
  have hn := norm_sub_le ((Real.exp (x.val * τ) : ℂ) * ψ τ)
    ((Real.exp (y.val * τ) : ℂ) * ψ τ)
  have hn0 := norm_nonneg ((Real.exp (x.val * τ) : ℂ) * ψ τ - (Real.exp (y.val * τ) : ℂ) * ψ τ)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hn
  have hp : 0 ≤ (Real.exp (x.val * τ) + Real.exp (y.val * τ)) * ‖ψ τ‖ := by positivity
  have hs := (sq_le_sq₀ hn0 hp).mpr (by nlinarith [hn])
  nlinarith [sq_nonneg ((Real.exp (x.val * τ) - Real.exp (y.val * τ)) * ‖ψ τ‖)]

private lemma hardyLineDensity_continuous {a b : ℝ} (ψ : HardySpace a b) :
    Continuous (hardyLineDensity ψ) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hdct : Tendsto (fun x : Icc a b => ∫ τ : ℝ,
      ‖(Real.exp (x.val * τ) : ℂ) * ψ τ - (Real.exp (y.val * τ) : ℂ) * ψ τ‖ ^ 2)
      (𝓝 y) (𝓝 0) := by
    convert tendsto_integral_filter_of_dominated_convergence (l := 𝓝 y)
      (fun τ : ℝ => 4 * (‖ψ τ‖ ^ 2 * hardyWeight a b τ))
      (F := fun x : Icc a b => fun τ : ℝ =>
        ‖(Real.exp (x.val * τ) : ℂ) * ψ τ - (Real.exp (y.val * τ) : ℂ) * ψ τ‖ ^ 2)
      (f := fun _ : ℝ => (0 : ℝ)) ?_ ?_
      ((hardySpace_integrable_weighted_sq ψ).const_mul 4) ?_ using 1 <;> try simp only [integral_zero]
    · exact Eventually.of_forall (fun x : Icc a b =>
        ((hardy_weighted_line_memLp x.property ψ).sub
          (hardy_weighted_line_memLp y.property ψ)).aestronglyMeasurable.norm.pow 2)
    · exact Eventually.of_forall (fun x => Eventually.of_forall (fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hardyLineDensity_diff_bound ψ x y τ))
    · apply Eventually.of_forall
      intro τ
      have h : Continuous (fun x : Icc a b =>
        ‖(Real.exp (x.val * τ) : ℂ) * ψ τ - (Real.exp (y.val * τ) : ℂ) * ψ τ‖ ^ 2) := by fun_prop
      simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h.tendsto y
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hdct
  simp only [Real.sqrt_zero] at hs
  convert hs using 1
  funext x
  have hfx := hardy_weighted_line_memLp x.property ψ
  have hfy := hardy_weighted_line_memLp y.property ψ
  change ‖hfx.toLp _ - hfy.toLp _‖ = _
  rw [← MemLp.toLp_sub]
  exact toLp_norm_eq_sqrt_integral (hfx.sub hfy)


private lemma physicalFourierL2_coe_classical {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    physicalFourierL2 (hf2.toLp f) =ᵐ[volume] (fun t : ℝ =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * 𝓕 f (-t / (2 * Real.pi))) := by
  let c : ℝ := -(2 * Real.pi)⁻¹
  have hc : c ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hq : QuasiMeasurePreserving (fun t : ℝ => c * t) volume volume :=
    (realScale_measurePreserving hc).quasiMeasurePreserving.mono_right Measure.smul_absolutelyContinuous
  have he := hq.ae_eq_comp (classical_fourier_eq_L2_ae hf hf2)
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)
    (rescaleL2 c hc (𝓕 (hf2.toLp f))), rescaleL2_coe c hc (𝓕 (hf2.toLp f)), he] with t ht hr he
  change physicalFourierL2 (hf2.toLp f) t = _
  change (_ • rescaleL2 c hc (𝓕 (hf2.toLp f))) t = _
  rw [ht]
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hr he ⊢
  rw [hr, ← he]
  congr 2
  dsimp [c]
  ring

private def hardyCompletedLine {a b : ℝ} (ψ : HardySpace a b) (x : Icc a b) :
    Lp ℂ 2 (volume : Measure ℝ) := physicalFourierL2 (hardyLineDensity ψ x)

private lemma hardyCompletedLine_continuous {a b : ℝ} (ψ : HardySpace a b) :
    Continuous (hardyCompletedLine ψ) :=
  physicalFourierL2_continuous.comp (hardyLineDensity_continuous ψ)

private lemma hardyCompletedLine_interior {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (x : Ioo a b) :
    hardyCompletedLine ψ ⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩ =
      (hardy_interiorLine_memLp hab x.property ψ).toLp _ := by
  apply Lp.ext
  have h := physicalFourierL2_coe_classical (hardy_weighted_line_integrable x.property ψ)
    (hardy_weighted_line_memLp ⟨x.property.1.le, x.property.2.le⟩ ψ)
  filter_upwards [h, (hardy_interiorLine_memLp hab x.property ψ).coeFn_toLp] with t ht ht'
  change physicalFourierL2 _ t = _
  dsimp only [hardyLineDensity]
  rw [ht, ht', fourierLaplace_line_eq_classical_fourier]

/-- Endpoint `L²` limits of the Fourier–Laplace representation, with the original filters. -/
theorem hardy_boundaryTraces_exist {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    ∃ p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun x : Ioo a b => (hardy_interiorLine_memLp hab x.property ψ).toLp
        (fun t : ℝ => fourierLaplace ψ (line x t)))
        (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 p.1) ∧
      Tendsto (fun x : Ioo a b => (hardy_interiorLine_memLp hab x.property ψ).toLp
        (fun t : ℝ => fourierLaplace ψ (line x t)))
        (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 p.2) := by
  refine ⟨(hardyCompletedLine ψ ⟨a, ⟨le_rfl, hab.le⟩⟩,
    hardyCompletedLine ψ ⟨b, ⟨hab.le, le_rfl⟩⟩), ?_, ?_⟩
  · have he : Tendsto (fun x : Ioo a b =>
        (⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩ : Icc a b))
        (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 ⟨a, ⟨le_rfl, hab.le⟩⟩) := by
      rw [tendsto_subtype_rng]
      exact (tendsto_comap.mono_right nhdsWithin_le_nhds)
    have h := ((hardyCompletedLine_continuous ψ).tendsto ⟨a, ⟨le_rfl, hab.le⟩⟩).comp he
    simpa only [Function.comp_def, hardyCompletedLine_interior hab ψ] using h
  · have he : Tendsto (fun x : Ioo a b =>
        (⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩ : Icc a b))
        (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 ⟨b, ⟨hab.le, le_rfl⟩⟩) := by
      rw [tendsto_subtype_rng]
      exact (tendsto_comap.mono_right nhdsWithin_le_nhds)
    have h := ((hardyCompletedLine_continuous ψ).tendsto ⟨b, ⟨hab.le, le_rfl⟩⟩).comp he
    simpa only [Function.comp_def, hardyCompletedLine_interior hab ψ] using h


private lemma rescaleL2_norm_sq (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖rescaleL2 c hc f‖ ^ 2 = |c⁻¹| * ‖f‖ ^ 2 := by
  rw [L2_norm_sq_integral]
  calc
    _ = ∫ t : ℝ, ‖f (c * t)‖ ^ 2 :=
      integral_congr_ae ((rescaleL2_coe c hc f).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    _ = |c⁻¹| * ∫ t : ℝ, ‖f t‖ ^ 2 := by
      simpa only [smul_eq_mul] using (Measure.integral_comp_mul_left (fun t : ℝ => ‖f t‖ ^ 2) c)
    _ = _ := by rw [← L2_norm_sq_integral]

private lemma physicalFourierL2_norm_sq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖physicalFourierL2 f‖ ^ 2 = ‖f‖ ^ 2 := by
  unfold physicalFourierL2
  rw [norm_smul, mul_pow, rescaleL2_norm_sq, Lp.norm_fourier_eq]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), inv_neg, inv_inv,
    abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  field_simp

private lemma hardyCompletedLine_norm_sq {a b : ℝ} (ψ : HardySpace a b) (x : Icc a b) :
    ‖hardyCompletedLine ψ x‖ ^ 2 = ∫ τ : ℝ, ‖ψ τ‖ ^ 2 * Real.exp (2 * x.val * τ) := by
  rw [hardyCompletedLine, physicalFourierL2_norm_sq, L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(hardy_weighted_line_memLp x.property ψ).coeFn_toLp] with τ ht
  change ‖(hardyLineDensity ψ x) τ‖ ^ 2 = _
  dsimp only [hardyLineDensity]
  rw [ht]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat]
  rw [show 2 * (x.val * τ) = 2 * x.val * τ by ring]
  exact mul_comm _ _

/-- The two endpoint norms have exactly the paper's sum normalization. -/
theorem hardy_boundary_norm_of_traces {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (left right : Lp ℂ 2 (volume : Measure ℝ))
    (hl : Tendsto (fun x : Ioo a b => (hardy_interiorLine_memLp hab x.property ψ).toLp
      (fun t : ℝ => fourierLaplace ψ (line x t)))
      (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 left))
    (hr : Tendsto (fun x : Ioo a b => (hardy_interiorLine_memLp hab x.property ψ).toLp
      (fun t : ℝ => fourierLaplace ψ (line x t)))
      (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 right)) :
    ‖ψ‖ ^ 2 = ‖left‖ ^ 2 + ‖right‖ ^ 2 := by
  have ha : NeBot (comap (Subtype.val : Ioo a b → ℝ) (nhdsWithin a (Ioo a b))) :=
    (left_nhdsWithin_Ioo_neBot hab).comap_of_range_mem (by simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : Ioo a b ∈ nhdsWithin a (Ioo a b)))
  have hb : NeBot (comap (Subtype.val : Ioo a b → ℝ) (nhdsWithin b (Ioo a b))) :=
    (right_nhdsWithin_Ioo_neBot hab).comap_of_range_mem (by simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : Ioo a b ∈ nhdsWithin b (Ioo a b)))
  letI := ha
  letI := hb
  have hleft : Tendsto (fun x : Ioo a b =>
      (⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩ : Icc a b))
      (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 ⟨a, ⟨le_rfl, hab.le⟩⟩) := by
    rw [tendsto_subtype_rng]
    exact tendsto_comap.mono_right nhdsWithin_le_nhds
  have hright : Tendsto (fun x : Ioo a b =>
      (⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩ : Icc a b))
      (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 ⟨b, ⟨hab.le, le_rfl⟩⟩) := by
    rw [tendsto_subtype_rng]
    exact tendsto_comap.mono_right nhdsWithin_le_nhds
  have hl' := ((hardyCompletedLine_continuous ψ).tendsto ⟨a, ⟨le_rfl, hab.le⟩⟩).comp hleft
  have hr' := ((hardyCompletedLine_continuous ψ).tendsto ⟨b, ⟨hab.le, le_rfl⟩⟩).comp hright
  simp only [Function.comp_def, hardyCompletedLine_interior hab ψ] at hl' hr'
  rw [tendsto_nhds_unique hl hl', tendsto_nhds_unique hr hr',
    hardyCompletedLine_norm_sq, hardyCompletedLine_norm_sq, hardySpace_norm_sq_integral]
  have hia := (hardy_weighted_line_memLp (x := a) ⟨le_rfl, hab.le⟩ ψ).norm.integrable_sq
  have hib := (hardy_weighted_line_memLp (x := b) ⟨hab.le, le_rfl⟩ ψ).norm.integrable_sq
  have ha' : Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * Real.exp (2 * a * τ)) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hia
  have hb' : Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * Real.exp (2 * b * τ)) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hib
  rw [← integral_add ha' hb']
  apply integral_congr_ae
  exact Eventually.of_forall (fun τ => by simp only [hardyWeight, mul_add])

end ConditionalGoldbach
