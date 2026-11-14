module

public import ConditionalGoldbach.Proofs.WideCounting
public import ConditionalGoldbach.Proofs.FiniteCharacterMoments

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma experiment_totient : Nat.totient experimentN=5760 := by
  change Nat.totient (2*(3*(5*(7*(11*13)))))=5760
  rw [Nat.totient_mul (by decide : Nat.Coprime 2 (3*(5*(7*(11*13))))),
    Nat.totient_mul (by decide : Nat.Coprime 3 (5*(7*(11*13)))),
    Nat.totient_mul (by decide : Nat.Coprime 5 (7*(11*13))),
    Nat.totient_mul (by decide : Nat.Coprime 7 (11*13)),
    Nat.totient_mul (by decide : Nat.Coprime 11 13)]
  norm_num [Nat.totient_prime (by decide : Nat.Prime 2),Nat.totient_prime (by decide : Nat.Prime 3),
    Nat.totient_prime (by decide : Nat.Prime 5),Nat.totient_prime (by decide : Nat.Prime 7),
    Nat.totient_prime (by decide : Nat.Prime 11),Nat.totient_prime (by decide : Nat.Prime 13)]

lemma countingCoefficient_eq_weight (n : ℕ) : countingCoefficient n =
    (Real.sqrt (experimentN:ℝ))⁻¹*mangoldt n*wideWeight (n/experimentN) := by
  by_cases hn : n=0
  · subst n
    simp [countingCoefficient,mangoldt]
  have hnr : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnS : Real.sqrt (n:ℝ)≠0 := (Real.sqrt_pos.mpr hnr).ne'
  have hNS : Real.sqrt (experimentN:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num [experimentN])).ne'
  unfold countingCoefficient wideWeight
  rw [Real.sqrt_div hnr.le]
  field_simp

lemma countingCoefficient_product (n m : ℕ) :
    countingCoefficient n*countingCoefficient m = (experimentN:ℝ)⁻¹*
      (mangoldt n*mangoldt m*wideWeight (n/experimentN)*wideWeight (m/experimentN)) := by
  rw [countingCoefficient_eq_weight,countingCoefficient_eq_weight]
  have hh : (Real.sqrt (experimentN:ℝ))⁻¹*(Real.sqrt (experimentN:ℝ))⁻¹=(experimentN:ℝ)⁻¹ := by
    rw [← mul_inv,← pow_two,Real.sq_sqrt (by norm_num [experimentN] : (0:ℝ)≤experimentN)]
  calc
    _ = ((Real.sqrt (experimentN:ℝ))⁻¹*(Real.sqrt (experimentN:ℝ))⁻¹)*
      (mangoldt n*mangoldt m*wideWeight (n/experimentN)*wideWeight (m/experimentN)) := by ring
    _ = _ := by rw [hh]

lemma wideCorrelation_counting : wideCorrelation =
    ∑ n ∈ Finset.range (experimentN+1), if 0<n ∧ n<experimentN ∧ Nat.Coprime (n*(experimentN-n)) experimentN
      then countingCoefficient n*countingCoefficient (experimentN-n) else 0 := by
  unfold wideCorrelation goldbach
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs
  · exact (countingCoefficient_product n (experimentN-n)).symm
  · simp

lemma counting_full_energy : diagonalCountingMoment=approxDiagonalMoment countingIntegral := by
  have h := finite_full_projection experimentN countingCoefficient countingCoefficient_zero
    (countingCoefficient_of_large (le_refl _))
  rw [experiment_totient] at h
  simp only [Finset.sum_range_succ (n := experimentN),countingCoefficient_of_large (le_refl experimentN),Complex.ofReal_zero,
    zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0),ite_self] at h
  simpa only [diagonalCountingMoment,approxDiagonalMoment,countingIntegral_exact,norm_neg,Nat.cast_ofNat] using h.symm

lemma counting_signed_energy : wideCorrelation=approxSignedMoment countingIntegral := by
  let V : Character experimentN → ℝ := fun χ => ‖∑ n ∈ Finset.range experimentN, (countingCoefficient n:ℂ)*χ n‖^2
  have hf := finite_full_projection experimentN countingCoefficient countingCoefficient_zero
    (countingCoefficient_of_large (le_refl _))
  have ho := finite_odd_projection experimentN (by decide) (by norm_num [experimentN])
    countingCoefficient countingCoefficient_zero (countingCoefficient_of_large (le_refl _))
  rw [experiment_totient] at hf ho
  rw [← wideCorrelation_counting] at ho
  simp only [Finset.sum_range_succ (n := experimentN),countingCoefficient_of_large (le_refl experimentN),Complex.ofReal_zero,
    zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0),ite_self] at hf ho
  change (5760:ℝ)⁻¹*(∑ χ, V χ)=diagonalCountingMoment at hf
  change (2/(5760:ℝ))*(∑ χ ∈ oddCharacters experimentN, V χ)=diagonalCountingMoment-wideCorrelation at ho
  have hs := signed_character_energy experimentN V
  unfold approxSignedMoment
  simp only [countingIntegral_exact,norm_neg]
  change wideCorrelation=(5760:ℝ)⁻¹*(∑ χ, (χ (-1)).re*V χ)
  rw [hs]
  linarith

theorem lemma_B_2 :
    (∀ χ : Character experimentN,
      Integrable (fun t : ℝ => (experimentN : ℂ) ^ (line 1 t) *
        mellin (fun u => (wideCompanion u : ℂ)) (line 1 t) * logDerivative χ (line 1 t)) ∧
      countingIntegral χ = -∑ n ∈ Finset.range experimentN, (countingCoefficient n : ℂ) * χ n) ∧
    wideCorrelation = approxSignedMoment countingIntegral ∧
    diagonalCountingMoment = approxDiagonalMoment countingIntegral  := by
  exact ⟨fun χ => ⟨countingIntegral_integrable χ,countingIntegral_exact χ⟩,counting_signed_energy,counting_full_energy⟩

end ConditionalGoldbach
