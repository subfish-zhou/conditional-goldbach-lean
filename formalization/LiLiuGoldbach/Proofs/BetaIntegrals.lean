import LiLiuGoldbach.BaseDefinitions

/-! The three exact beta integrals and their absolute convergence. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma beta_substitution_image (h : ℝ) (hh : 0 < h) :
    (fun u : ℝ => h * u / (1 - u)) '' Ioo 0 1 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact div_pos (mul_pos hh hu.1) (sub_pos.mpr hu.2)
  · intro hx
    change 0 < x at hx
    refine ⟨x / (h + x), ?_, ?_⟩
    · constructor
      · exact div_pos hx (by linarith)
      · exact (div_lt_one (by linarith)).2 (by linarith)
    · have hd : h + x ≠ 0 := ne_of_gt (by linarith)
      have hx' : 1 - x / (h + x) ≠ 0 := by
        apply ne_of_gt
        exact sub_pos.mpr ((div_lt_one (by linarith)).2 (by linarith))
      field_simp [hh.ne']
      <;> ring

lemma beta_substitution_injective (h : ℝ) (hh : 0 < h) :
    Set.InjOn (fun u : ℝ => h * u / (1 - u)) (Ioo 0 1) := by
  intro u hu v hv heq
  have hu0 : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu.2)
  have hv0 : 1 - v ≠ 0 := ne_of_gt (sub_pos.mpr hv.2)
  have he := (div_eq_div_iff hu0 hv0).mp heq
  nlinarith

lemma beta_substitution_deriv (h u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ => h * u / (1 - u)) (h / (1 - u) ^ 2) u := by
  convert ((hasDerivAt_id u).const_mul h).fun_div ((hasDerivAt_const u 1).sub (hasDerivAt_id u))
    (ne_of_gt (sub_pos.mpr hu.2)) using 1 <;> simp only [Pi.div_apply, Pi.sub_apply, id_eq] <;> ring

lemma beta_substitution_integrand (h : ℝ) (hh : 0 < h) (s z : ℂ)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    (h / (1 - u) ^ 2 : ℝ) •
      (((h * u / (1 - u) : ℝ) : ℂ) ^ (-1 / 2 - s) *
        ((h * u / (1 - u) + h : ℝ) : ℂ) ^ (-1 / 2 - z)) =
    (h : ℂ) ^ (-(s + z)) *
      ((u : ℂ) ^ ((1 / 2 - s) - 1) * (1 - (u : ℂ)) ^ ((s + z) - 1)) := by
  have hv : 0 < 1 - u := sub_pos.mpr hu.2
  have hc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hvC : (1 - (u : ℂ)) ≠ 0 := by exact_mod_cast hv.ne'
  have hsum : h * u / (1 - u) + h = h / (1 - u) := by field_simp; ring
  rw [hsum]
  simp only [Complex.real_smul, Complex.ofReal_div]
  rw [Complex.div_cpow_ofReal_nonneg (mul_pos hh hu.1).le hv.le,
    Complex.div_cpow_ofReal_nonneg hh.le hv.le,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hh.le hu.1.le]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  have he1 : -1 / 2 - s = (1 / 2 - s) - 1 := by ring
  rw [he1]
  have hpH : (h : ℂ) * ((h : ℂ) ^ ((1 / 2 - s) - 1) * (h : ℂ) ^ (-1 / 2 - z)) =
      (h : ℂ) ^ (-(s + z)) := by
    calc
      _ = (h : ℂ) ^ (1 : ℂ) * ((h : ℂ) ^ ((1 / 2 - s) - 1) *
          (h : ℂ) ^ (-1 / 2 - z)) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_add _ _ hc, ← Complex.cpow_add _ _ hc]
        congr 1
        ring
  have hpV : (1 - (u : ℂ)) ^ (2 : ℕ) *
      ((1 - (u : ℂ)) ^ ((1 / 2 - s) - 1) * (1 - (u : ℂ)) ^ (-1 / 2 - z)) =
      (1 - (u : ℂ)) ^ (1 - (s + z)) := by
    rw [← Complex.cpow_add _ _ hvC, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hvC]
    congr 1
    ring
  calc
    _ = (h : ℂ) * ((h : ℂ) ^ ((1 / 2 - s) - 1) * (h : ℂ) ^ (-1 / 2 - z)) *
        (u : ℂ) ^ ((1 / 2 - s) - 1) /
      ((1 - (u : ℂ)) ^ (2 : ℕ) *
        ((1 - (u : ℂ)) ^ ((1 / 2 - s) - 1) * (1 - (u : ℂ)) ^ (-1 / 2 - z))) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ = _ := by
      have hvInv : ((1 - (u : ℂ)) ^ (1 - (s + z)))⁻¹ =
          (1 - (u : ℂ)) ^ ((s + z) - 1) := by
        rw [← Complex.cpow_neg]
        congr 1
        ring
      rw [hpH, hpV, div_eq_mul_inv, hvInv]
      ring

lemma beta_difference_integral (h : ℝ) (hh : 0 < h) (s z : ℂ) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - s) * (x + h : ℂ) ^ (-1 / 2 - z)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (s + z) := by
  rw [← beta_substitution_image h hh]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (beta_substitution_deriv h u hu).hasDerivWithinAt)
    (beta_substitution_injective h hh)]
  calc
    _ = ∫ u in Ioo (0 : ℝ) 1, (h : ℂ) ^ (-(s + z)) *
        ((u : ℂ) ^ ((1 / 2 - s) - 1) * (1 - (u : ℂ)) ^ ((s + z) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      rw [abs_of_pos (div_pos hh (sq_pos_of_pos (sub_pos.mpr hu.2)))]
      simpa only [Complex.ofReal_add] using beta_substitution_integrand h hh s z u hu
    _ = _ := by
      rw [integral_const_mul, betaIntegral,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]

lemma beta_sum_integral (h : ℝ) (hh : 0 < h) (s z : ℂ) :
    (∫ x in Ioo (0 : ℝ) h, (x : ℂ) ^ (-1 / 2 - s) * (h - x : ℂ) ^ (-1 / 2 - z)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (1 / 2 - z) := by
  have he1 : (1 / 2 - s : ℂ) - 1 = -1 / 2 - s := by ring
  have he2 : (1 / 2 - z : ℂ) - 1 = -1 / 2 - z := by ring
  have he3 : (1 / 2 - s : ℂ) + (1 / 2 - z) - 1 = -(s + z) := by ring
  simpa only [intervalIntegral.integral_of_le hh.le, integral_Ioc_eq_integral_Ioo,
    he1, he2, he3, Complex.ofReal_sub] using Complex.betaIntegral_scaled (1 / 2 - s) (1 / 2 - z) hh

lemma beta_difference_integrable (h : ℝ) (hh : 0 < h) (s z : ℂ)
    (hd : (s, z) ∈ betaDomain) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (x + h : ℂ) ^ (-1 / 2 - z)) (Ioi 0) := by
  have hs : 0 < (1 / 2 - s).re := by simp only [sub_re]; norm_num; linarith [hd.1]
  have hz : 0 < (s + z).re := hd.2.2
  have hi := Complex.betaIntegral_convergent hs hz
  rw [← beta_substitution_image h hh,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun u hu => (beta_substitution_deriv h u hu).hasDerivWithinAt)
      (beta_substitution_injective h hh)]
  apply IntegrableOn.congr_fun ((hi.1.mono_set Ioo_subset_Ioc_self).const_mul ((h : ℂ) ^ (-(s + z))))
  · intro u hu
    dsimp only
    rw [abs_of_pos (div_pos hh (sq_pos_of_pos (sub_pos.mpr hu.2)))]
    simpa only [Complex.ofReal_add] using (beta_substitution_integrand h hh s z u hu).symm
  · exact measurableSet_Ioo

lemma beta_sum_integrable (h : ℝ) (hh : 0 < h) (s z : ℂ)
    (hd : (s, z) ∈ betaDomain) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (h - x : ℂ) ^ (-1 / 2 - z)) (Ioo 0 h) := by
  have hs : 0 < (1 / 2 - s).re := by simp only [sub_re]; norm_num; linarith [hd.1]
  have hz : 0 < (1 / 2 - z).re := by simp only [sub_re]; norm_num; linarith [hd.2.1]
  have hi := Complex.betaIntegral_convergent hs hz
  have hi' := hi.comp_mul_right (c := h⁻¹)
  simp only [zero_div, one_div, inv_inv, ← div_eq_mul_inv] at hi'
  have he1 : (1 / 2 - s : ℂ) - 1 = -1 / 2 - s := by ring
  have he2 : (1 / 2 - z : ℂ) - 1 = -1 / 2 - z := by ring
  try simp only [he1, he2] at hi'
  apply IntegrableOn.congr_fun ((hi'.1.mono_set Ioo_subset_Ioc_self).const_mul
    ((h : ℂ) ^ ((-1 / 2 - s) + (-1 / 2 - z))))
  · intro x hx
    dsimp only
    have hxh : 0 ≤ x / h := (div_pos hx.1 hh).le
    have hrest : 0 ≤ 1 - x / h := sub_nonneg.mpr ((div_le_one hh).2 hx.2.le)
    have hc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
    calc
      _ = ((h : ℂ) ^ (-1 / 2 - s) * ((x / h : ℝ) : ℂ) ^ (-1 / 2 - s)) *
          ((h : ℂ) ^ (-1 / 2 - z) * ((1 - x / h : ℝ) : ℂ) ^ (-1 / 2 - z)) := by
        rw [Complex.cpow_add _ _ hc]
        simp only [Complex.ofReal_sub, Complex.ofReal_one]
        ring
      _ = (h * (x / h) : ℝ) ^ (-1 / 2 - s) * (h * (1 - x / h) : ℝ) ^ (-1 / 2 - z) := by
        simp only [Complex.ofReal_mul]
        rw [Complex.mul_cpow_ofReal_nonneg hh.le hxh,
          Complex.mul_cpow_ofReal_nonneg hh.le hrest]
      _ = _ := by
        congr 2
        · field_simp
        · push_cast
          field_simp
  · exact measurableSet_Ioo

theorem lemma_4_1 (h : ℝ) (hh : 0 < h) (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - s) * (x + h : ℂ) ^ (-1 / 2 - z)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (s + z) ∧
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-1 / 2 - z) * (x + h : ℂ) ^ (-1 / 2 - s)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - z) (s + z) ∧
    (∫ x in Ioo (0 : ℝ) h, (x : ℂ) ^ (-1 / 2 - s) * (h - x : ℂ) ^ (-1 / 2 - z)) =
      (h : ℂ) ^ (-(s + z)) * betaIntegral (1 / 2 - s) (1 / 2 - z) := by
  exact ⟨beta_difference_integral h hh s z,
    by simpa [add_comm] using beta_difference_integral h hh z s,
    beta_sum_integral h hh s z⟩

theorem lemma_4_1_absolute_convergence (h : ℝ) (hh : 0 < h)
    (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (x + h : ℂ) ^ (-1 / 2 - z)) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - z) *
      (x + h : ℂ) ^ (-1 / 2 - s)) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-1 / 2 - s) *
      (h - x : ℂ) ^ (-1 / 2 - z)) (Ioo 0 h) := by
  exact ⟨beta_difference_integrable h hh s z hd,
    beta_difference_integrable h hh z s ⟨hd.2.1, hd.1, by simpa [add_comm] using hd.2.2⟩,
    beta_sum_integrable h hh s z hd⟩

theorem lemma_4_1_signed_model (h : ℝ) (hh : 0 < h)
    (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    let I₁ := ∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (-1 / 2 - s) * (x + h : ℂ) ^ (-1 / 2 - z)
    let I₂ := ∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (-1 / 2 - z) * (x + h : ℂ) ^ (-1 / 2 - s)
    let I₃ := ∫ x in Ioo (0 : ℝ) h,
      (x : ℂ) ^ (-1 / 2 - s) * (h - x : ℂ) ^ (-1 / 2 - z)
    I₁ + I₂ - I₃ = (h : ℂ) ^ (-(s + z)) * betaKernel s z ∧
    ∀ N k : ℕ, Even N → 4 ≤ N → 0 < k → h = (k * N : ℕ) →
      (singularSeries (k * N) : ℂ) * (I₁ + I₂ - I₃) =
        singularSeries (k * N) * (h : ℂ) ^ (-(s + z)) * betaKernel s z := by
  dsimp only
  obtain ⟨h₁, h₂, h₃⟩ := lemma_4_1 h hh s z hd
  rw [h₁, h₂, h₃]
  constructor
  · unfold betaKernel
    ring
  · intro N k hN hN4 hk hhN
    unfold betaKernel
    ring

end LiLiuGoldbach16
