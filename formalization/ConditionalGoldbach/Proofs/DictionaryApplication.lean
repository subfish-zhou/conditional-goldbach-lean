module

public import ConditionalGoldbach.Proofs.SpectralDictionary
public import ConditionalGoldbach.AnalyticPrerequisites

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff Quaternion
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

theorem spectralWidthFromBound_spec (N : ℕ) (M : ℝ)
    (hδ : 0 < spectralScale N) (hM : spectralScale N < M) :
    0 < spectralWidthFromBound N M ∧ spectralWidthFromBound N M < 1 / 2 ∧
      spectralWidthFromBound N M * (1 - spectralWidthFromBound N M) =
        spectralScale N ^ 2 / (4 * M ^ 2) := by
  have hMpos : 0 < M := lt_trans hδ hM
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hMpos
  have hratio : 0 < spectralScale N ^ 2 / M ^ 2 := div_pos (sq_pos_of_pos hδ) hM2
  have hratio_one : spectralScale N ^ 2 / M ^ 2 < 1 := by
    apply (div_lt_one hM2).2
    exact (sq_lt_sq₀ hδ.le hMpos.le).2 hM
  have harg : 0 < 1 - spectralScale N ^ 2 / M ^ 2 := sub_pos.mpr hratio_one
  have hr : 0 < Real.sqrt (1 - spectralScale N ^ 2 / M ^ 2) := Real.sqrt_pos.2 harg
  have hr2 := Real.sq_sqrt harg.le
  have hrlt : Real.sqrt (1 - spectralScale N ^ 2 / M ^ 2) < 1 := by
    nlinarith
  unfold spectralWidthFromBound
  refine ⟨by linarith, by linarith, ?_⟩
  rw [show spectralScale N ^ 2 / (4 * M ^ 2) = (spectralScale N ^ 2 / M ^ 2) / 4 by ring]
  nlinarith


/-- The paper's Hardy-space dictionary, obtained from its spectral realization. -/
theorem theorem_6_1 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    (SpectralR N (alpha N) ha ↔ ‖residualOperator ha N‖ ≤ spectralScale N) ∧
    (∀ η : ℝ, 0 < η → η < 1 / 2 →
      (SpectralZeroFree N (alpha N) ha η ↔
        ‖residualOperator ha N‖ ≤ spectralScale N / (2 * Real.sqrt (η * (1 - η))))) ∧
    (∀ M : ℝ, spectralScale N < M → ‖residualOperator ha N‖ ≤ M →
      0 < spectralWidthFromBound N M ∧ spectralWidthFromBound N M < 1 / 2 ∧
      SpectralZeroFree N (alpha N) ha (spectralWidthFromBound N M)) := by
  have hparam := large_parameters hlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hδ := spectralScale_pos N hNpos (singularSeries_pos N) hparam.2.1
  have hT := residualOperator_has_spectral_data N hN hlarge hGRH ha
  have hd := theorem_6_1_abstract_dictionary N (residualOperator ha N) hT hδ
  refine ⟨hd.1, hd.2, ?_⟩
  intro M hM hnorm
  obtain ⟨hηpos, hηhalf, hidentity⟩ := spectralWidthFromBound_spec N M hδ hM
  refine ⟨hηpos, hηhalf, ?_⟩
  apply (hd.2 _ hηpos hηhalf).2
  apply hnorm.trans
  have hMpos : 0 < M := lt_trans hδ hM
  have hprod : 0 < spectralWidthFromBound N M * (1 - spectralWidthFromBound N M) :=
    mul_pos hηpos (by linarith)
  have hh := (eigenvalue_bound_iff_parameter (spectralScale N) M _ hδ hMpos.ne' hprod).2
    (le_of_eq hidentity)
  simpa only [abs_of_pos hMpos] using hh

end ConditionalGoldbach
