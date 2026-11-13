import ConditionalGoldbach.Proofs.HardyHolomorphic

/-! Paired vertical means and the original Hardy supremum norm. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform
open scoped Topology
namespace ConditionalGoldbach

lemma l2_norm_sq_integral {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ t : ℝ, ‖f t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma classical_fourier_norm_sq_integral {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (∫ t : ℝ, ‖𝓕 f t‖ ^ 2) = ∫ t : ℝ, ‖f t‖ ^ 2 := by
  calc
    _ = ∫ t : ℝ, ‖(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) t‖ ^ 2 :=
      integral_congr_ae ((classical_fourier_eq_L2_ae hf hf2).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    _ = ‖(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 := (l2_norm_sq_integral _).symm
    _ = ‖hf2.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ t : ℝ, ‖(hf2.toLp f) t‖ ^ 2 := l2_norm_sq_integral _
    _ = _ := integral_congr_ae (hf2.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖ ^ 2))

lemma fourierLaplace_line_normIntegral {a b x : ℝ} (hx : x ∈ Ioo a b) (ψ : HardySpace a b) :
    (∫ t : ℝ, ‖fourierLaplace ψ (line x t)‖ ^ 2) =
      ∫ τ : ℝ, ‖ψ τ‖ ^ 2 * Real.exp (2 * x * τ) := by
  let f : ℝ → ℂ := fun τ => (Real.exp (x * τ) : ℂ) * ψ τ
  let c : ℝ := -(2 * Real.pi)⁻¹
  let k : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)⁻¹
  have hf : Integrable f := hardy_weighted_line_integrable hx ψ
  have hf2 : MemLp f 2 := hardy_weighted_line_memLp ⟨hx.1.le, hx.2.le⟩ ψ
  calc
    _ = ‖k‖ ^ 2 * ∫ t : ℝ, ‖𝓕 f (c * t)‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [fourierLaplace_line_eq_classical_fourier, norm_mul, mul_pow]
        change ‖k‖ ^ 2 * ‖𝓕 f (-t / (2 * Real.pi))‖ ^ 2 = _
        rw [show -t / (2 * Real.pi) = c * t by dsimp [c]; ring])
    _ = ‖k‖ ^ 2 * (|c⁻¹| * ∫ t : ℝ, ‖𝓕 f t‖ ^ 2) := by
      congr 1
      simpa only [smul_eq_mul] using (Measure.integral_comp_mul_left (fun t : ℝ => ‖𝓕 f t‖ ^ 2) c)
    _ = ∫ τ : ℝ, ‖f τ‖ ^ 2 := by
      rw [classical_fourier_norm_sq_integral hf hf2]
      dsimp [k, c]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), inv_neg, inv_inv,
        abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      field_simp
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun τ => by
        dsimp [f]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm])

lemma hardy_paired_exp_le {a b ε : ℝ} (hab : a < b) (hε : 0 ≤ ε) (hε' : ε ≤ b - a) (τ : ℝ) :
    Real.exp (2 * (a + ε) * τ) + Real.exp (2 * (b - ε) * τ) ≤ hardyWeight a b τ := by
  let t : ℝ := ε / (b - a)
  have ht : 0 ≤ t := div_nonneg hε (sub_pos.mpr hab).le
  have ht' : t ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr hε'
  have hx := convexOn_exp.2 (mem_univ (2 * a * τ)) (mem_univ (2 * b * τ))
    (show 0 ≤ 1 - t by linarith) ht (by ring : 1 - t + t = 1)
  have hy := convexOn_exp.2 (mem_univ (2 * a * τ)) (mem_univ (2 * b * τ))
    ht (show 0 ≤ 1 - t by linarith) (by ring : t + (1 - t) = 1)
  have hxarg : (1 - t) * (2 * a * τ) + t * (2 * b * τ) = 2 * (a + ε) * τ := by
    dsimp [t]
    field_simp
    ring
  have hyarg : t * (2 * a * τ) + (1 - t) * (2 * b * τ) = 2 * (b - ε) * τ := by
    dsimp [t]
    field_simp
    ring
  simp only [smul_eq_mul, hxarg, hyarg] at hx hy
  unfold hardyWeight
  linarith

lemma fourierLaplace_paired_integral_le {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < (b - a) / 2) :
    Integrable (fun t : ℝ => ‖fourierLaplace ψ (line (a + ε) t)‖ ^ 2 +
      ‖fourierLaplace ψ (line (b - ε) t)‖ ^ 2) ∧
    (∫ t : ℝ, ‖fourierLaplace ψ (line (a + ε) t)‖ ^ 2 +
      ‖fourierLaplace ψ (line (b - ε) t)‖ ^ 2) ≤ ‖ψ‖ ^ 2 := by
  have hxa : a + ε ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hxb : b - ε ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hia := (interiorLine_memLp hab hxa ψ).norm.integrable_sq
  have hib := (interiorLine_memLp hab hxb ψ).norm.integrable_sq
  refine ⟨hia.add hib, ?_⟩
  rw [integral_add hia hib, fourierLaplace_line_normIntegral hxa,
    fourierLaplace_line_normIntegral hxb, hardySpace_norm_sq_integral]
  have hga := (hardy_weighted_line_memLp ⟨hxa.1.le, hxa.2.le⟩ ψ).norm.integrable_sq
  have hgb := (hardy_weighted_line_memLp ⟨hxb.1.le, hxb.2.le⟩ ψ).norm.integrable_sq
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    ← Real.exp_nat_mul, Nat.cast_ofNat] at hga hgb
  have hga' : Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * Real.exp (2 * (a + ε) * τ)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hga
  have hgb' : Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * Real.exp (2 * (b - ε) * τ)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hgb
  rw [← integral_add hga' hgb']
  apply integral_mono_ae (hga'.add hgb') (hardySpace_integrable_weighted_sq ψ)
  exact Eventually.of_forall (fun τ => by
    dsimp only [Pi.add_apply]
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hardy_paired_exp_le hab hε.le (by linarith) τ) (sq_nonneg _))

lemma fourierLaplace_isRawHardy {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    IsRawHardy a b (fourierLaplace ψ) :=
  ⟨fourierLaplace_differentiableOn ψ, ‖ψ‖ ^ 2,
    fun ε hε hε' => fourierLaplace_paired_integral_le hab ψ hε hε'⟩


lemma hardy_density_line_integrable {a b x : ℝ} (hx : x ∈ Icc a b) (ψ : HardySpace a b) :
    Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * Real.exp (2 * x * τ)) := by
  have h := (hardy_weighted_line_memLp hx ψ).norm.integrable_sq
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using h

lemma fourierLaplace_paired_integral_eq {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < (b - a) / 2) :
    (∫ t : ℝ, ‖fourierLaplace ψ (line (a + ε) t)‖ ^ 2 +
      ‖fourierLaplace ψ (line (b - ε) t)‖ ^ 2) =
    ∫ τ : ℝ, ‖ψ τ‖ ^ 2 * (Real.exp (2 * (a + ε) * τ) + Real.exp (2 * (b - ε) * τ)) := by
  have hxa : a + ε ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hxb : b - ε ∈ Ioo a b := ⟨by linarith, by linarith⟩
  rw [integral_add (interiorLine_memLp hab hxa ψ).norm.integrable_sq
    (interiorLine_memLp hab hxb ψ).norm.integrable_sq,
    fourierLaplace_line_normIntegral hxa, fourierLaplace_line_normIntegral hxb,
    ← integral_add (hardy_density_line_integrable ⟨hxa.1.le, hxa.2.le⟩ ψ)
      (hardy_density_line_integrable ⟨hxb.1.le, hxb.2.le⟩ ψ)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun τ => by simp only [Pi.add_apply, mul_add])

lemma fourierLaplace_paired_integral_tendsto {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, ‖fourierLaplace ψ (line (a + ε) t)‖ ^ 2 +
      ‖fourierLaplace ψ (line (b - ε) t)‖ ^ 2) (𝓝[>] 0) (𝓝 (‖ψ‖ ^ 2)) := by
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < (b - a) / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < (b - a) / 2 by linarith)))] with ε hε hε'
    exact ⟨hε, hε'⟩
  have hdct := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (F := fun ε : ℝ => fun τ : ℝ => ‖ψ τ‖ ^ 2 *
      (Real.exp (2 * (a + ε) * τ) + Real.exp (2 * (b - ε) * τ)))
    (f := fun τ : ℝ => ‖ψ τ‖ ^ 2 * hardyWeight a b τ)
    (fun τ : ℝ => ‖ψ τ‖ ^ 2 * hardyWeight a b τ)
    (Eventually.of_forall (fun ε => ((hardySpace_aestronglyMeasurable ψ).norm.pow 2).mul
      (by fun_prop : Continuous (fun τ : ℝ =>
        Real.exp (2 * (a + ε) * τ) + Real.exp (2 * (b - ε) * τ))).aestronglyMeasurable))
    ?_ (hardySpace_integrable_weighted_sq ψ) ?_
  · have heq : (fun ε : ℝ => ∫ t : ℝ, ‖fourierLaplace ψ (line (a + ε) t)‖ ^ 2 +
        ‖fourierLaplace ψ (line (b - ε) t)‖ ^ 2) =ᶠ[𝓝[>] 0]
        (fun ε : ℝ => ∫ τ : ℝ, ‖ψ τ‖ ^ 2 *
          (Real.exp (2 * (a + ε) * τ) + Real.exp (2 * (b - ε) * τ))) :=
      hsmall.mono (fun ε hε => fourierLaplace_paired_integral_eq hab ψ hε.1 hε.2)
    rw [← hardySpace_norm_sq_integral] at hdct
    exact hdct.congr' heq.symm
  · filter_upwards [hsmall] with ε hε
    exact Eventually.of_forall (fun τ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hardy_paired_exp_le hab hε.1.le (by linarith [hε.2]) τ)
        (sq_nonneg _))
  · exact Eventually.of_forall (fun τ => by
      have hc : Continuous (fun ε : ℝ => ‖ψ τ‖ ^ 2 *
          (Real.exp (2 * (a + ε) * τ) + Real.exp (2 * (b - ε) * τ))) := by fun_prop
      simpa only [add_zero, sub_zero, hardyWeight] using
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds)

lemma fourierLaplace_rawHardyNormSq {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    rawHardyNormSq a b (fourierLaplace ψ) = ‖ψ‖ ^ 2 := by
  let S : Set ℝ := {r | ∃ ε : ℝ, 0 < ε ∧ ε < (b - a) / 2 ∧
    r = ∫ t : ℝ, ‖fourierLaplace ψ (line (a + ε) t)‖ ^ 2 +
      ‖fourierLaplace ψ (line (b - ε) t)‖ ^ 2}
  change sSup S = ‖ψ‖ ^ 2
  have hne : S.Nonempty := by
    refine ⟨_, (b - a) / 4, by linarith, by linarith, rfl⟩
  have hbound : ∀ r ∈ S, r ≤ ‖ψ‖ ^ 2 := by
    rintro r ⟨ε, hε, hε', rfl⟩
    exact (fourierLaplace_paired_integral_le hab ψ hε hε').2
  have hBdd : BddAbove S := ⟨‖ψ‖ ^ 2, hbound⟩
  apply le_antisymm (csSup_le hne hbound)
  apply le_of_tendsto (fourierLaplace_paired_integral_tendsto hab ψ)
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < (b - a) / 2 by linarith)))] with ε hε hε'
  exact le_csSup hBdd ⟨ε, hε, hε', rfl⟩

/-- The forward and isometric halves of the paper's Fourier–Laplace lemma. -/
lemma lemma_5_2_forward (a b : ℝ) (hab : a < b) (ψ : HardySpace a b) :
    IsRawHardy a b (fourierLaplace ψ) ∧
    rawHardyNormSq a b (fourierLaplace ψ) = ‖ψ‖ ^ 2 ∧
    ‖ψ‖ ^ 2 = ‖(boundaryTraces hab ψ).1‖ ^ 2 + ‖(boundaryTraces hab ψ).2‖ ^ 2 :=
  ⟨fourierLaplace_isRawHardy hab ψ, fourierLaplace_rawHardyNormSq hab ψ, boundaryTraces_norm_sq hab ψ⟩

end ConditionalGoldbach
