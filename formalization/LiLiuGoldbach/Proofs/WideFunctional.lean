import LiLiuGoldbach.Proofs.FiniteFunctional
import LiLiuGoldbach.Proofs.WideWeight

/-! The actual finite-smooth wide weight defines a bounded Hardy functional and its Riesz vector. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma experimentN_large : Real.exp 10 < (experimentN : ℝ) := by
  have he : Real.exp 1 < (11/4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc
    Real.exp 10 = Real.exp 1^10 := by simpa using Real.exp_nat_mul (1 : ℝ) 10
    _ < (11/4 : ℝ)^10 := pow_lt_pow_left₀ he (Real.exp_pos _).le (by norm_num)
    _ < experimentN := by norm_num [experimentN]

lemma wide_sigmaStar_mem : sigmaStar ∈ Ioo (alpha experimentN) beta := by
  have hlog : 10 < Real.log experimentN :=
    (Real.lt_log_iff_exp_lt (by norm_num [experimentN])).mpr experimentN_large
  constructor
  · unfold sigmaStar alpha
    apply (div_lt_div_iff₀ (by linarith : 0 < Real.log experimentN) (by norm_num : (0 : ℝ) < 9)).mpr
    linarith
  · norm_num [sigmaStar,beta]

lemma wideFunctional_integrable (ψ : HardySpace (alpha experimentN) beta) :
    Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line sigmaStar t) *
      mellin (fun u => (wideCompanion u : ℂ)) (line sigmaStar t) *
      (1 + line sigmaStar t) * fourierLaplace ψ (line sigmaStar t)) :=
  finiteFunctionalValue_integrable experimentN (by norm_num [experimentN])
    wideCompanion (wideCompanion_contDiff.of_le (by norm_num)) _ _
    (wideCompanion_support.trans Ioo_subset_Icc_self) sigmaStar (by norm_num [sigmaStar])
    wide_sigmaStar_mem ψ

lemma wideFunctional_riesz_exists : ∃ v : HardySpace (alpha experimentN) beta,
    ∀ ψ, wideFunctional ψ = paperInner ψ v := by
  obtain ⟨v,hv⟩ := finite_functional_riesz_exists (a := alpha experimentN)
    experimentN (by norm_num [experimentN]) wideCompanion
    (wideCompanion_contDiff.of_le (by norm_num)) (16/experimentN) (1-16/experimentN)
    (by norm_num [experimentN]) (wideCompanion_support.trans Ioo_subset_Icc_self)
  exact ⟨v,hv sigmaStar (by norm_num [sigmaStar]) wide_sigmaStar_mem⟩

lemma wideRieszVector_spec (ψ : HardySpace (alpha experimentN) beta) :
    wideFunctional ψ = paperInner ψ wideRieszVector := by
  unfold wideRieszVector
  rw [dif_pos wideFunctional_riesz_exists]
  exact Classical.choose_spec wideFunctional_riesz_exists ψ

lemma wideFunctional_continuousLinearMap :
    ∃ ℓ : HardySpace (alpha experimentN) beta →L[ℂ] ℂ, ∀ h, ℓ h = wideFunctional h := by
  refine ⟨InnerProductSpace.toDual ℂ _ wideRieszVector, ?_⟩
  intro ψ
  exact (wideRieszVector_spec ψ).symm

end LiLiuGoldbach16
