import ConditionalGoldbach.Proofs.SpectralAlgebra

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Square summability controls the perturbation of each complex product factor. -/
theorem spectralComplex_term_summable (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : ℂ) :
    Summable (fun j => (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q)) := by
  have hs : Summable (fun j => (eigenvalues T j ^ 2 : ℂ)) := by
    exact_mod_cast (Complex.summable_ofReal.mpr (eigenvalues_square_summable T hT))
  have hc := ((hs.mul_left (4 / (spectralScale N : ℂ) ^ 2)).mul_right q).mul_right (1 - q)
  convert hc using 1
  funext j
  push_cast
  ring

/-- The complex spectral product converges at every point. -/
theorem spectralComplex_multipliable (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : ℂ) :
    Multipliable (fun j => 1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q)) := by
  simpa only [sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable (spectralComplex_term_summable N T hT q).neg

/-- There are no additional zeros created by a convergent complex spectral product. -/
theorem spectralComplex_eq_zero_iff_factor (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : ℂ) :
    spectralComplex N T q = 0 ↔
      ∃ j, 1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q) = 0 := by
  constructor
  · intro hz
    by_contra hn
    push Not at hn
    have hne := tprod_one_add_ne_zero_of_summable
      (f := fun j => -((4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q)))
      (by simpa only [sub_eq_add_neg] using hn)
      ((spectralComplex_term_summable N T hT q).neg.norm)
    apply hne
    simpa only [spectralComplex, sub_eq_add_neg] using hz
  · intro hz
    exact (hasProd_zero_of_exists_eq_zero hz).tprod_eq

theorem spectralFactor_map (f : ℂ →ₐ[ℝ] Quaternion ℝ) (a : ℝ) (q : ℂ) :
    1 - a • (f q * (1 - f q)) = f (1 - (a : ℂ) * q * (1 - q)) := by
  have hf : f (a : ℂ) = (a : Quaternion ℝ) := f.commutes a
  simp only [map_sub, map_mul, map_one, hf, Algebra.smul_def]
  rw [mul_assoc]
  rfl
theorem spectralPartialQuaternion_map (N : ℕ) (T : H →L[ℂ] H)
    (f : ℂ →ₐ[ℝ] Quaternion ℝ) (q : ℂ) (k : ℕ) :
    spectralPartialQuaternion N T (f q) k =
      f (∏ j ∈ Finset.range k,
        (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))) := by
  induction k with
  | zero => simp [spectralPartialQuaternion]
  | succ k ih =>
    have hrec (q : Quaternion ℝ) :
      spectralPartialQuaternion N T q (k + 1) = spectralPartialQuaternion N T q k *
        (1 - (4 * eigenvalues T k ^ 2 / spectralScale N ^ 2 : ℝ) • (q * (1 - q))) := by
      simp [spectralPartialQuaternion, List.range_succ, List.foldl_append]
    rw [hrec, ih, Finset.prod_range_succ, map_mul]
    congr 1
    exact spectralFactor_map f _ q
theorem quaternion_exists_complex_slice (q : Quaternion ℝ) : ∃ f : ℂ →ₐ[ℝ] Quaternion ℝ, ∃ z : ℂ, f z = q := by
  by_cases him : q.im = 0
  · refine ⟨Quaternion.ofComplex, (q.re : ℂ), ?_⟩
    have h := Quaternion.re_add_im q
    simpa only [Quaternion.coe_ofComplex, Quaternion.coeComplex_coe, him, add_zero] using h
  · let J : Quaternion ℝ := ‖q.im‖⁻¹ • q.im
    have hJim : J.im = J := by
      dsimp [J]
      rw [Quaternion.im_smul]
      rfl
    have hJnorm : ‖J‖ = 1 := by
      dsimp [J]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr him)
    have hJsq : J * J = -1 := by
      calc
        J * J = J.im ^ 2 := by rw [hJim, pow_two]
        _ = -((Quaternion.normSq J.im : ℝ) : Quaternion ℝ) := Quaternion.im_sq J
        _ = -1 := by rw [hJim, Quaternion.normSq_eq_norm_mul_self, hJnorm]; norm_num
    refine ⟨Complex.liftAux J hJsq, ⟨q.re, ‖q.im‖⟩, ?_⟩
    change (q.re : Quaternion ℝ) + ‖q.im‖ • (‖q.im‖⁻¹ • q.im) = q
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr him), one_smul]
    exact Quaternion.re_add_im q
theorem spectralPartialQuaternion_tendsto_map (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (f : ℂ →ₐ[ℝ] Quaternion ℝ) (q : ℂ) :
    Tendsto (spectralPartialQuaternion N T (f q)) atTop (𝓝 (f (spectralComplex N T q))) := by
  have hc : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  have ht := hc.continuousAt.tendsto.comp
    (spectralComplex_multipliable N T hT q).hasProd.tendsto_prod_nat
  convert ht using 1
  · funext k
    exact spectralPartialQuaternion_map N T f q k
  · rfl

theorem spectralQuaternion_apply_algHom (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (f : ℂ →ₐ[ℝ] Quaternion ℝ) (q : ℂ) :
    spectralQuaternion N T (f q) = f (spectralComplex N T q) := by
  have hconv := spectralPartialQuaternion_tendsto_map N T hT f q
  have hex : ∃ y, Tendsto (spectralPartialQuaternion N T (f q)) atTop (𝓝 y) := ⟨_, hconv⟩
  unfold spectralQuaternion
  rw [dite_eq_left hex]
  exact tendsto_nhds_unique (Classical.choose_spec hex) hconv

theorem spectralPartialQuaternion_tendsto (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : Quaternion ℝ) :
    Tendsto (spectralPartialQuaternion N T q) atTop (𝓝 (spectralQuaternion N T q)) := by
  obtain ⟨f, z, rfl⟩ := quaternion_exists_complex_slice q
  rw [spectralQuaternion_apply_algHom N T hT f z]
  exact spectralPartialQuaternion_tendsto_map N T hT f z

theorem spectralQuaternion_eq_zero_iff_factor (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : Quaternion ℝ) :
    spectralQuaternion N T q = 0 ↔
      ∃ j, 1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) • (q * (1 - q)) = 0 := by
  obtain ⟨f, z, rfl⟩ := quaternion_exists_complex_slice q
  rw [spectralQuaternion_apply_algHom N T hT f z, map_eq_zero,
    spectralComplex_eq_zero_iff_factor N T hT z]
  apply exists_congr
  intro j
  rw [spectralFactor_map, map_eq_zero]

theorem spectralQuaternion_complex_slice (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : ℂ) :
    spectralQuaternion N T (complexQuaternion q) = complexQuaternion (spectralComplex N T q) :=
  spectralQuaternion_apply_algHom N T hT Quaternion.ofComplex q

theorem complex_quadratic_factor_zero_iff (δ μ : ℝ) (hδ : δ ≠ 0) (q : ℂ) :
    1 - (4 * μ ^ 2 / δ ^ 2 : ℝ) * q * (1 - q) = 0 ↔
      μ ≠ 0 ∧ q * (1 - q) = (δ ^ 2 / (4 * μ ^ 2) : ℝ) := by
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
  constructor
  · intro hz
    have hμ : μ ≠ 0 := by
      intro hzero
      simp [hzero] at hz
    refine ⟨hμ, ?_⟩
    have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
    push_cast at hz ⊢
    field_simp at hz ⊢
    linear_combination -hz
  · rintro ⟨hμ, heq⟩
    have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
    push_cast at heq ⊢
    field_simp at heq ⊢
    linear_combination -heq

/-- The complex zeros are exactly the roots of the nontrivial quadratic factors. -/
theorem spectralComplex_eq_zero_iff (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (hδ : spectralScale N ≠ 0) (q : ℂ) :
    spectralComplex N T q = 0 ↔ ∃ j, eigenvalues T j ≠ 0 ∧
      q * (1 - q) = (spectralScale N ^ 2 / (4 * eigenvalues T j ^ 2) : ℝ) := by
  rw [spectralComplex_eq_zero_iff_factor N T hT q]
  apply exists_congr
  intro j
  exact complex_quadratic_factor_zero_iff _ _ hδ q

/-- The same classification holds in every quaternionic slice. -/
theorem spectralQuaternion_eq_zero_iff (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (hδ : spectralScale N ≠ 0) (q : Quaternion ℝ) :
    spectralQuaternion N T q = 0 ↔ ∃ j, eigenvalues T j ≠ 0 ∧
      q * (1 - q) = (spectralScale N ^ 2 / (4 * eigenvalues T j ^ 2) : ℝ) := by
  obtain ⟨f, z, rfl⟩ := quaternion_exists_complex_slice q
  rw [spectralQuaternion_apply_algHom N T hT f z, map_eq_zero,
    spectralComplex_eq_zero_iff N T hT hδ z]
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  have hc : f ((spectralScale N ^ 2 / (4 * eigenvalues T j ^ 2) : ℝ) : ℂ) =
      ((spectralScale N ^ 2 / (4 * eigenvalues T j ^ 2) : ℝ) : Quaternion ℝ) := f.commutes _
  rw [← hc, ← map_one f, ← map_sub, ← map_mul]
  exact f.injective.eq_iff.symm

end ConditionalGoldbach

