module

public import ConditionalGoldbach.Proofs.DictionaryApplication

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology Quaternion
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem spectral_real_zero_mem_Ioo (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (hδ : 0 < spectralScale N) (x : ℝ)
    (hx : spectralQuaternion N T x = 0) : x ∈ Ioo 0 1 := by
  obtain ⟨j, hμ, hroot⟩ := (spectralQuaternion_eq_zero_iff N T hT hδ.ne' x).1 hx
  have hc : 0 < spectralScale N ^ 2 / (4 * eigenvalues T j ^ 2) :=
    div_pos (sq_pos_of_pos hδ) (mul_pos (by norm_num) (sq_pos_of_ne_zero hμ))
  have heq := congrArg (fun q : Quaternion ℝ => q.re) hroot
  simp only [Quaternion.re_mul, Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe,
    Quaternion.imK_coe, Quaternion.re_sub, Quaternion.re_one, Quaternion.imI_sub,
    Quaternion.imI_one, Quaternion.imJ_sub, Quaternion.imJ_one, Quaternion.imK_sub,
    Quaternion.imK_one, zero_mul, sub_zero] at heq
  constructor
  · by_contra hn
    have hxle : x ≤ 0 := le_of_not_gt hn
    have hp : x * (1 - x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxle (by linarith)
    linarith
  · by_contra hn
    have hxge : 1 ≤ x := le_of_not_gt hn
    have hp : x * (1 - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith

theorem proposition_6_3 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    (∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q = 0 ↔
      ∃ j : ℕ, eigenvalues (residualOperator ha N) j ≠ 0 ∧
        q * (1 - q) = (spectralScale N ^ 2 /
          (4 * eigenvalues (residualOperator ha N) j ^ 2) : ℝ)) ∧
    (∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q = 0 →
      q.re ≠ 1 / 2 → q = (q.re : Quaternion ℝ) ∧ q.re ∈ Ioo 0 1) ∧
    (∀ x : ℝ, spectralQuaternion N (residualOperator ha N) x = 0 → x ∈ Ioo 0 1) ∧
    Set.Finite {j | spectralScale N < |eigenvalues (residualOperator ha N) j|} := by
  have hparam := large_parameters hlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hδ := spectralScale_pos N hNpos (singularSeries_pos N) hparam.2.1
  have hT := residualOperator_has_spectral_data N hN hlarge hGRH ha
  refine ⟨spectralQuaternion_eq_zero_iff N _ hT hδ.ne', ?_,
    spectral_real_zero_mem_Ioo N _ hT hδ, finite_large_eigenvalues _ hT _ hδ⟩
  intro q hzero hcrit
  obtain ⟨j, hμ, hroot⟩ := (spectralQuaternion_eq_zero_iff N _ hT hδ.ne' q).1 hzero
  have hreal := quaternion_quadratic_real_of_off_critical q _ hroot hcrit
  refine ⟨hreal, spectral_real_zero_mem_Ioo N _ hT hδ q.re ?_⟩
  simpa only [← hreal] using hzero

set_option linter.unusedVariables false in
theorem proposition_6_1_all_slices (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (J : Quaternion ℝ) (hJre : J.re = 0) (hJsq : J ^ 2 = -1) (z : ℂ) :
    spectralQuaternion N (residualOperator ha N) ((z.re : Quaternion ℝ) + z.im • J) =
      ((spectralComplex N (residualOperator ha N) z).re : Quaternion ℝ) +
        (spectralComplex N (residualOperator ha N) z).im • J := by
  have hT := residualOperator_has_spectral_data N hN hlarge hGRH ha
  exact spectralQuaternion_apply_algHom N _ hT (Complex.liftAux J (by simpa [pow_two] using hJsq)) z

theorem proposition_6_1_complex_slice (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (q : ℂ) :
    spectralQuaternion N (residualOperator ha N) (complexQuaternion q) =
      complexQuaternion (spectralComplex N (residualOperator ha N) q) := by
  have hT := residualOperator_has_spectral_data N hN hlarge hGRH ha
  exact spectralQuaternion_complex_slice N _ hT q

end ConditionalGoldbach
