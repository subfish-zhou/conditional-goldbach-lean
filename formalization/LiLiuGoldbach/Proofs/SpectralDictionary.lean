import LiLiuGoldbach.Proofs.SpectralProducts

/-! The zero--operator-norm dictionary is proved from explicit spectral data.
No Hardy realization or GRH theorem is used in this module. -/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate Topology ContDiff Quaternion
open MeasureTheory Filter Set Complex
noncomputable section
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

theorem quaternion_quadratic_real_of_off_critical (q : Quaternion ℝ) (c : ℝ)
    (hroot : q * (1 - q) = (c : Quaternion ℝ)) (hcrit : q.re ≠ 1 / 2) :
    q = (q.re : Quaternion ℝ) := by
  have hI := congrArg (fun q : Quaternion ℝ => q.imI) hroot
  have hJ := congrArg (fun q : Quaternion ℝ => q.imJ) hroot
  have hK := congrArg (fun q : Quaternion ℝ => q.imK) hroot
  simp at hI hJ hK
  have hc : 1 - 2 * q.re ≠ 0 := by intro h; apply hcrit; linarith
  have hi : q.imI = 0 := by
    apply (mul_eq_zero.mp (show (1 - 2 * q.re) * q.imI = 0 by nlinarith [hI])).resolve_left hc
  have hj : q.imJ = 0 := by
    apply (mul_eq_zero.mp (show (1 - 2 * q.re) * q.imJ = 0 by nlinarith [hJ])).resolve_left hc
  have hk : q.imK = 0 := by
    apply (mul_eq_zero.mp (show (1 - 2 * q.re) * q.imK = 0 by nlinarith [hK])).resolve_left hc
  ext <;> simp [hi, hj, hk]

theorem quaternion_quadratic_critical_of_bound (q : Quaternion ℝ) (c : ℝ)
    (hroot : q * (1 - q) = (c : Quaternion ℝ)) (hc : 1 / 4 ≤ c) : q.re = 1 / 2 := by
  by_contra hn
  have hreal := quaternion_quadratic_real_of_off_critical q c hroot hn
  rw [hreal] at hroot
  have heq := congrArg (fun q : Quaternion ℝ => q.re) hroot
  simp at heq
  have hs : (q.re - 1 / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (q.re - 1 / 2)]
  have hz := sq_eq_zero_iff.mp hs
  exact hn (by linarith)

theorem quadratic_right_root (c : ℝ) (hc : c < 1 / 4) :
    ((1 + Real.sqrt (1 - 4 * c)) / 2) * (1 - (1 + Real.sqrt (1 - 4 * c)) / 2) = c ∧
      1 / 2 < (1 + Real.sqrt (1 - 4 * c)) / 2 := by
  have harg : 0 < 1 - 4 * c := by linarith
  have hs := Real.sq_sqrt harg.le
  have hp := Real.sqrt_pos.2 harg
  constructor <;> nlinarith

theorem norm_le_iff_eigenvalues {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) (M : ℝ) (hM : 0 ≤ M) :
    ‖T‖ ≤ M ↔ ∀ j, |eigenvalues T j| ≤ M := by
  simpa only [eigenvalues, dite_eq_left hT] using (Classical.choice hT).norm_le_iff M hM

theorem spectral_R_iff_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) (hδ : 0 < spectralScale N) :
    (∀ q : Quaternion ℝ, spectralQuaternion N T q = 0 → q.re = 1 / 2) ↔
      ‖T‖ ≤ spectralScale N := by
  constructor
  · intro hR
    apply (norm_le_iff_eigenvalues T hT _ hδ.le).2
    intro j
    by_contra hn
    have hgt : spectralScale N < |eigenvalues T j| := lt_of_not_ge hn
    have hμ : eigenvalues T j ≠ 0 := by
      intro hz
      simp only [hz, abs_zero] at hgt
      linarith
    have hμ2 : 0 < eigenvalues T j ^ 2 := sq_pos_of_ne_zero hμ
    let c := spectralScale N ^ 2 / (4 * eigenvalues T j ^ 2)
    have hc : c < 1 / 4 := by
      apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hμ2)).2
      have hs := (sq_lt_sq₀ hδ.le (abs_nonneg (eigenvalues T j))).2 hgt
      rw [sq_abs] at hs
      nlinarith
    obtain ⟨hroot, hhalf⟩ := quadratic_right_root c hc
    let x := (1 + Real.sqrt (1 - 4 * c)) / 2
    have hzero : spectralQuaternion N T (x : Quaternion ℝ) = 0 := by
      apply (spectralQuaternion_eq_zero_iff N T hT hδ.ne' _).2
      refine ⟨j, hμ, ?_⟩
      change (x : Quaternion ℝ) * (1 - (x : Quaternion ℝ)) = (c : Quaternion ℝ)
      simpa only [Quaternion.coe_mul, Quaternion.coe_sub, Quaternion.coe_one] using
        congrArg (fun y : ℝ => (y : Quaternion ℝ)) (show x * (1 - x) = c from hroot)
    have hr := hR (x : Quaternion ℝ) hzero
    change x = 1 / 2 at hr
    change 1 / 2 < x at hhalf
    linarith
  · intro hnorm q hzero
    obtain ⟨j, hμ, hroot⟩ := (spectralQuaternion_eq_zero_iff N T hT hδ.ne' q).1 hzero
    have hμ2 : 0 < eigenvalues T j ^ 2 := sq_pos_of_ne_zero hμ
    have hb := (abs_eigenvalues_le_norm T hT j).trans hnorm
    apply quaternion_quadratic_critical_of_bound q _ hroot
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hμ2)).2
    have hs := (sq_le_sq₀ (abs_nonneg (eigenvalues T j)) hδ.le).2 hb
    rw [sq_abs] at hs
    nlinarith

theorem eigenvalue_bound_iff_parameter (δ μ a : ℝ) (hδ : 0 < δ) (hμ : μ ≠ 0)
    (ha : 0 < a) : |μ| ≤ δ / (2 * Real.sqrt a) ↔ a ≤ δ ^ 2 / (4 * μ ^ 2) := by
  have hr := Real.sqrt_pos.2 ha
  have hd : 0 < 2 * Real.sqrt a := mul_pos (by norm_num) hr
  have hden : 0 < 4 * μ ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hμ)
  constructor
  · intro hb
    have hmul := (le_div_iff₀ hd).mp hb
    have hs := (sq_le_sq₀ (mul_nonneg (abs_nonneg μ) hd.le) hδ.le).2 hmul
    simp only [mul_pow, sq_abs, Real.sq_sqrt ha.le] at hs
    apply (le_div_iff₀ hden).2
    nlinarith
  · intro hp
    have hmul := (le_div_iff₀ hden).mp hp
    apply (le_div_iff₀ hd).2
    apply (sq_le_sq₀ (mul_nonneg (abs_nonneg μ) hd.le) hδ.le).mp
    simp only [mul_pow, sq_abs, Real.sq_sqrt ha.le]
    nlinarith
theorem spectral_zeroFree_iff_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) (hδ : 0 < spectralScale N)
    (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    (∀ q : Quaternion ℝ, 1 - η < q.re → spectralQuaternion N T q ≠ 0) ↔
      ‖T‖ ≤ spectralScale N / (2 * Real.sqrt (η * (1 - η))) := by
  have ha : 0 < η * (1 - η) := mul_pos hη (by linarith)
  have hM : 0 < spectralScale N / (2 * Real.sqrt (η * (1 - η))) :=
    div_pos hδ (mul_pos (by norm_num) (Real.sqrt_pos.2 ha))
  constructor
  · intro hzeroFree
    apply (norm_le_iff_eigenvalues T hT _ hM.le).2
    intro j
    by_cases hμ : eigenvalues T j = 0
    · simp only [hμ, abs_zero]
      exact hM.le
    · apply (eigenvalue_bound_iff_parameter _ _ _ hδ hμ ha).2
      by_contra hn
      let c := spectralScale N ^ 2 / (4 * eigenvalues T j ^ 2)
      have hclt : c < η * (1 - η) := lt_of_not_ge hn
      have hc : c < 1 / 4 := by nlinarith [sq_nonneg (η - 1 / 2)]
      obtain ⟨hroot, _⟩ := quadratic_right_root c hc
      have harg : 0 < 1 - 4 * c := by linarith
      have hs := Real.sq_sqrt harg.le
      have hsqrt : 1 - 2 * η < Real.sqrt (1 - 4 * c) := by
        by_contra hnot
        have hle : Real.sqrt (1 - 4 * c) ≤ 1 - 2 * η := le_of_not_gt hnot
        have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hle
        nlinarith
      let x := (1 + Real.sqrt (1 - 4 * c)) / 2
      have hxlarge : 1 - η < x := by dsimp [x]; linarith
      have hzero : spectralQuaternion N T (x : Quaternion ℝ) = 0 := by
        apply (spectralQuaternion_eq_zero_iff N T hT hδ.ne' _).2
        refine ⟨j, hμ, ?_⟩
        change (x : Quaternion ℝ) * (1 - (x : Quaternion ℝ)) = (c : Quaternion ℝ)
        simpa only [Quaternion.coe_mul, Quaternion.coe_sub, Quaternion.coe_one] using
          congrArg (fun y : ℝ => (y : Quaternion ℝ)) (show x * (1 - x) = c from hroot)
      exact hzeroFree (x : Quaternion ℝ) hxlarge hzero
  · intro hnorm q hlarge hzero
    obtain ⟨j, hμ, hroot⟩ := (spectralQuaternion_eq_zero_iff N T hT hδ.ne' q).1 hzero
    have hcrit : q.re ≠ 1 / 2 := by intro heq; rw [heq] at hlarge; linarith
    have hreal := quaternion_quadratic_real_of_off_critical q _ hroot hcrit
    have hb := (abs_eigenvalues_le_norm T hT j).trans hnorm
    have hc := (eigenvalue_bound_iff_parameter _ _ _ hδ hμ ha).1 hb
    rw [hreal] at hroot
    have heq := congrArg (fun q : Quaternion ℝ => q.re) hroot
    simp only [Quaternion.re_mul, Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe,
      Quaternion.imK_coe, Quaternion.re_sub, Quaternion.re_one, Quaternion.imI_sub,
      Quaternion.imI_one, Quaternion.imJ_sub, Quaternion.imJ_one, Quaternion.imK_sub,
      Quaternion.imK_one, zero_mul, sub_zero] at heq
    have hp : 0 < (q.re - η) * (q.re - (1 - η)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

theorem theorem_6_1_abstract_dictionary {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (hδ : 0 < spectralScale N) :
    ((∀ q : Quaternion ℝ, spectralQuaternion N T q = 0 → q.re = 1 / 2) ↔
      ‖T‖ ≤ spectralScale N) ∧
    ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ((∀ q : Quaternion ℝ, 1 - η < q.re → spectralQuaternion N T q ≠ 0) ↔
        ‖T‖ ≤ spectralScale N / (2 * Real.sqrt (η * (1 - η)))) := by
  exact ⟨spectral_R_iff_norm N T hT hδ, spectral_zeroFree_iff_norm N T hT hδ⟩
end LiLiuGoldbach16
