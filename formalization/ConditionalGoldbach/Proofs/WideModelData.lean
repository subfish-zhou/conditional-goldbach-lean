module

public import ConditionalGoldbach.Proofs.FiniteModelBasic

/-! Exact compatibility of the Appendix B weight with the finite C6 model interfaces. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory Set
namespace ConditionalGoldbach

def wideFiniteModelWeight : FiniteModelWeight wideWeight where
  smooth := wideWeight_contDiff
  lower := 16/experimentN
  upper := 1-16/experimentN
  lower_pos := by norm_num [experimentN]
  upper_lt_one := by norm_num [experimentN]
  lower_le_upper := by norm_num [experimentN]
  support_subset := wideWeight_support.trans Ioo_subset_Icc_self

lemma companion_wideWeight : companion wideWeight = wideCompanion := by
  funext u
  by_cases hu : 0 < u
  · have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
    simp only [companion,wideWeight]
    field_simp
  · have hz : wideCompanion u = 0 := by
      by_contra hn
      have hh := (wideCompanion_support hn).1
      have hpos : (0 : ℝ) < 16/experimentN := by norm_num [experimentN]
      exact hu (hpos.trans hh)
    simp [companion,wideWeight,hz]

lemma finiteModel_mass_wideWeight : FiniteModel.modelMass wideWeight = wideModelMass := rfl

lemma mellinWeight_wideWeight : mellinWeight wideWeight =
    mellin (fun u => (wideCompanion u : ℂ)) := by
  unfold mellinWeight
  rw [companion_wideWeight]

end ConditionalGoldbach
