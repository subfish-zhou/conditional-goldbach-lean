import LiLiuGoldbach.Proofs.WideWeight
import LiLiuGoldbach.Proofs.FiniteMellinProjection

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma countingCoefficient_zero : countingCoefficient 0=0 := by simp [countingCoefficient,mangoldt]

lemma countingCoefficient_of_large {n : ℕ} (hn : experimentN≤n) : countingCoefficient n=0 := by
  have hz : wideCompanion ((n:ℝ)/experimentN)=0 := by
    by_contra he
    have hs := (wideCompanion_support he).2
    have hn' : (1:ℝ)≤(n:ℝ)/experimentN := (one_le_div (by norm_num [experimentN])).mpr (by exact_mod_cast hn)
    have hp : (0:ℝ)<16/experimentN := by norm_num [experimentN]
    linarith
  simp only [countingCoefficient,hz,mul_zero]

lemma counting_mellin_term (χ : Character experimentN) (n : ℕ) :
    ((mangoldt n:ℂ)*χ n/(n:ℂ)^(1/2:ℂ))*(wideCompanion (n/experimentN):ℂ)=
      (countingCoefficient n:ℂ)*χ n := by
  by_cases hn : n=0
  · subst n
    simp [countingCoefficient,mangoldt]
  have hnr : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh : (n:ℂ)^(1/2:ℂ)=(Real.sqrt n:ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hnr.le]
    congr 1
    norm_num
  rw [hh]
  unfold countingCoefficient
  push_cast
  ring

lemma countingIntegral_integrable (χ : Character experimentN) :
    Integrable (fun t : ℝ => (experimentN:ℂ)^(line 1 t)*
      mellin (fun u => (wideCompanion u:ℂ)) (line 1 t)*logDerivative χ (line 1 t)) :=
  finite_character_mellin_initial_integrable χ wideCompanion (wideCompanion_contDiff.of_le (by norm_num))
    _ _ (wideCompanion_support.trans Ioo_subset_Icc_self) 1 (by norm_num)

lemma countingIntegral_exact (χ : Character experimentN) :
    countingIntegral χ = -∑ n ∈ Finset.range experimentN, (countingCoefficient n:ℂ)*χ n := by
  let F : ℕ → ℂ := fun n => (countingCoefficient n:ℂ)*χ n
  let G : ℕ → ℂ → ℂ := fun n s =>
    (mangoldt (n+1):ℂ)*χ (n+1)/(n+1:ℕ)^(1/2:ℂ)*mellin (fun u => (wideCompanion u:ℂ)) s*
      (((n+1:ℕ)/(experimentN:ℝ):ℝ):ℂ)^(-s)
  have hs := finite_mellin_inversion_hasSum wideCompanion (wideCompanion_contDiff.of_le (by norm_num))
    _ _ (wideCompanion_support.trans Ioo_subset_Icc_self) 1 (by norm_num)
    (fun n : ℕ => (n+1:ℕ)/(experimentN:ℝ))
    (fun n : ℕ => (mangoldt (n+1):ℂ)*χ (n+1)/(n+1:ℕ)^(1/2:ℂ))
    (fun n => by norm_num [experimentN]; positivity) (character_mellin_coeff_summable χ 1 (by norm_num))
  have hs1 : HasSum (fun n => F (n+1)) (verticalMellin 1 (fun s => ∑' n, G n s)) := by
    convert hs using 1
    funext n
    simpa only [F,Nat.cast_add,Nat.cast_one] using (counting_mellin_term χ (n+1)).symm
  have hs0 : HasSum F (verticalMellin 1 (fun s => ∑' n, G n s)) := by
    have h := (hasSum_nat_add_iff 1).mp hs1
    simpa [F,countingCoefficient_zero] using h
  have he : (verticalMellin 1 (fun s => ∑' n, G n s)) = -countingIntegral χ := by
    unfold countingIntegral
    unfold verticalMellin
    rw [← mul_neg,← integral_neg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    exact finite_character_mellin_series χ wideCompanion (line 1 t) (by norm_num [line])
  have ht : ∑' n, F n = ∑ n ∈ Finset.range experimentN, F n := by
    apply tsum_eq_sum
    intro n hn
    have hn' : experimentN≤n := by simpa only [Finset.mem_range,not_lt] using hn
    simp [F,countingCoefficient_of_large hn']
  have hh := hs0.tsum_eq
  rw [he,ht] at hh
  simpa only [neg_neg] using (congrArg Neg.neg hh).symm

end LiLiuGoldbach16
