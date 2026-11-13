import LiLiuGoldbach.Proofs.WidePrimePowerCount
import LiLiuGoldbach.Proofs.MomentError

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
open Set
namespace LiLiuGoldbach16

theorem lemma_B_3 (Ihat : Character experimentN → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : (5760 : ℝ)⁻¹ * ∑ χ : Character experimentN, ‖countingIntegral χ - Ihat χ‖ ^ 2 ≤ ε ^ 2) :
    |wideCorrelation - approxSignedMoment Ihat| ≤
      2 * Real.sqrt (approxDiagonalMoment Ihat) * ε + ε ^ 2 ∧
    |(unorderedPrimePairs : ℝ) - approxPrimeCount Ihat| ≤ countError Ihat ε ∧
    (unorderedPrimePairs : ℝ) ∈
      Icc (approxPrimeCount Ihat - countError Ihat ε) (approxPrimeCount Ihat + countError Ihat ε) ∩
        Set.range (fun k : ℤ => (k : ℝ)) := by
  have h := wideSignedMoment_error Ihat ε hε herr
  have hcount := proposition_B_1.2.2.2.2
  have he : (unorderedPrimePairs:ℝ)-approxPrimeCount Ihat=
      ((experimentN:ℝ)/2)*(wideCorrelation-approxSignedMoment Ihat) := by
    rw [hcount]
    unfold approxPrimeCount
    ring
  have hbound : |(unorderedPrimePairs:ℝ)-approxPrimeCount Ihat|≤countError Ihat ε := by
    rw [he,abs_mul,abs_of_nonneg (by norm_num [experimentN] : 0≤(experimentN:ℝ)/2)]
    exact mul_le_mul_of_nonneg_left h (by norm_num [experimentN])
  refine ⟨h,hbound,⟨?_,⟨(unorderedPrimePairs:ℤ),by exact Int.cast_natCast unorderedPrimePairs⟩⟩⟩
  obtain ⟨hl,hu⟩ := abs_le.mp hbound
  constructor <;> linarith

end LiLiuGoldbach16
