module

public import ConditionalGoldbach.Proofs.HardyInterior

/-! Construction of the endpoint Fourier–Laplace traces by L² limits. -/
public section

noncomputable section
open MeasureTheory Filter Set Complex FourierTransform
open scoped Topology
namespace ConditionalGoldbach
open Analysis

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


private lemma hardyCompletedLine_norm_sq {a b : ℝ} (ψ : HardySpace a b) (x : Icc a b) :
    ‖hardyCompletedLine ψ x‖ ^ 2 = ∫ τ : ℝ, ‖ψ τ‖ ^ 2 * Real.exp (2 * x.val * τ) := by
  rw [hardyCompletedLine, physicalFourierL2_norm_sq, L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(hardy_weighted_line_memLp x.property ψ).coeFn_toLp] with τ ht
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
  let := ha
  let := hb
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
