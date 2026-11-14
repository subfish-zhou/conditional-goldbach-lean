module

public import ConditionalGoldbach.Proofs.FiniteCharacterShift
public import ConditionalGoldbach.Proofs.FiniteMellinDouble
public import ConditionalGoldbach.Proofs.MellinDiagonal
public import ConditionalGoldbach.Proofs.WideMoments
public import ConditionalGoldbach.Proofs.WideModelData

/-! The finite-smooth arithmetic double Mellin projections for Appendix B. -/
public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma countingIntegral_star (χ : Character experimentN) :
    countingIntegral (star χ)=conj (countingIntegral χ) := by
  simp only [countingIntegral_exact,map_neg,map_sum,map_mul,
    Complex.conj_ofReal,MulChar.star_apply,RCLike.star_def]

lemma counting_odd_energy :
    (2/(experimentN.totient:ℝ))*∑ χ∈oddCharacters experimentN, ‖countingIntegral χ‖^2 =
      diagonalCountingMoment-wideCorrelation := by
  have ho := finite_odd_projection experimentN (by decide) (by norm_num [experimentN])
    countingCoefficient countingCoefficient_zero (countingCoefficient_of_large (le_refl _))
  rw [← wideCorrelation_counting] at ho
  simp only [Finset.sum_range_succ (n := experimentN),countingCoefficient_of_large (le_refl experimentN),Complex.ofReal_zero,
    zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0),ite_self] at ho
  simpa only [diagonalCountingMoment,countingIntegral_exact,norm_neg] using ho

lemma countingIntegral_shift (hGRH : GRH experimentN) (χ : Character experimentN)
    (hχ : χ∈oddCharacters experimentN) (σ : ℝ) (hσ : 0<σ) (hσ1 : σ≤1) :
    Integrable (fun t : ℝ => (experimentN:ℂ)^(line σ t)*
      mellin (fun u => (wideCompanion u:ℂ)) (line σ t)*logDerivative χ (line σ t)) ∧
    verticalMellin σ (fun s => (experimentN:ℂ)^s*
      mellin (fun u => (wideCompanion u:ℂ)) s*logDerivative χ s)=countingIntegral χ := by
  exact finite_character_mellin_shift (by norm_num [experimentN]) hGRH χ hχ wideCompanion
    (wideCompanion_contDiff.of_le (by norm_num)) _ _
    (wideCompanion_support.trans Ioo_subset_Icc_self) σ hσ hσ1

lemma wide_character_mellin (hGRH : GRH experimentN) (σ : ℝ) (hσ : 0<σ) (hσ1 : σ≤1) :
    Integrable (fun p : ℝ×ℝ => (experimentN:ℂ)^(line σ p.1+line σ p.2)*
      mellin (fun u => (wideCompanion u:ℂ)) (line σ p.1)*
      mellin (fun u => (wideCompanion u:ℂ)) (line σ p.2)*characterKernel experimentN (line σ p.1) (line σ p.2)) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z => (experimentN:ℂ)^(s+z)*
      mellin (fun u => (wideCompanion u:ℂ)) s*mellin (fun u => (wideCompanion u:ℂ)) z*
      characterKernel experimentN s z))=(diagonalCountingMoment-wideCorrelation:ℝ) := by
  have hfac (s z : ℂ) := weighted_characterKernel_factor experimentN wideWeight s z
  simp only [mellinWeight_wideWeight] at hfac
  have hi (χ : Character experimentN) (hχ : χ∈oddCharacters experimentN) :=
    countingIntegral_shift hGRH χ hχ σ hσ hσ1
  have hs (χ : Character experimentN) (hχ : χ∈oddCharacters experimentN) :=
    countingIntegral_shift hGRH (star χ) ((star_mem_oddCharacters χ).mpr hχ) σ hσ hσ1
  constructor
  · simp_rw [hfac]
    exact (integrable_finsetSum _ (fun χ hχ => (hi χ hχ).1.mul_prod (hs χ hχ).1)).const_mul _
  · simp_rw [hfac]
    rw [double_verticalMellin_finset_prod (oddCharacters experimentN) σ _ _ _
      (fun χ hχ => (hi χ hχ).1) (fun χ hχ => (hs χ hχ).1)]
    have he (χ : Character experimentN) (hχ : χ∈oddCharacters experimentN) :
        verticalMellin σ (fun s => (experimentN:ℂ)^s*mellin (fun u => (wideCompanion u:ℂ)) s*logDerivative χ s)*
        verticalMellin σ (fun z => (experimentN:ℂ)^z*mellin (fun u => (wideCompanion u:ℂ)) z*logDerivative (star χ) z)=
        (‖countingIntegral χ‖^2:ℝ) := by
      rw [(hi χ hχ).2,(hs χ hχ).2,countingIntegral_star,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl he]
    simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_natCast,Complex.ofReal_sum,Complex.ofReal_pow] using congrArg Complex.ofReal counting_odd_energy

lemma wide_diagonal_term (n : ℕ) :
    ((mangoldt n:ℂ)^2/(n:ℂ))*(wideCompanion (n/experimentN):ℂ)^2=(countingCoefficient n:ℂ)^2 := by
  by_cases hn : n=0
  · subst n
    simp [mangoldt,countingCoefficient]
  have hp : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hz : (Real.sqrt (n:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  have he : (Real.sqrt (n:ℝ):ℂ)^2=(n:ℂ) := by exact_mod_cast Real.sq_sqrt hp.le
  simp only [countingCoefficient,Complex.ofReal_mul,Complex.ofReal_div,mul_pow,div_pow]
  rw [he]

lemma wide_diagonal_tsum :
    (∑' k : ℕ, (if Nat.Coprime (k+1) experimentN then
      (mangoldt (k+1):ℂ)^2/(k+1:ℕ) else 0)*(wideCompanion ((k+1:ℕ)/experimentN):ℂ)^2)=
      (diagonalCountingMoment:ℂ) := by
  let f : ℕ→ℂ := fun n => if Nat.Coprime n experimentN then (countingCoefficient n:ℂ)^2 else 0
  have hz : ∀n∉Finset.range experimentN, f n=0 := by
    intro n hn
    have hh : experimentN≤n := by simpa only [Finset.mem_range,not_lt] using hn
    simp [f,countingCoefficient_of_large hh]
  have hf : Summable f := summable_of_ne_finset_zero hz
  have ht (k : ℕ) : (if Nat.Coprime (k+1) experimentN then (mangoldt (k+1):ℂ)^2/(k+1:ℕ) else 0)*
      (wideCompanion ((k+1:ℕ)/experimentN):ℂ)^2=f (k+1) := by
    dsimp [f]
    split_ifs
    · exact wide_diagonal_term _
    · simp
  simp_rw [ht]
  have h0 : f 0=0 := by simp [f]
  rw [← zero_add (∑' k, f (k+1)),← h0,← hf.tsum_eq_zero_add,tsum_eq_sum hz]
  simp only [diagonalCountingMoment,Complex.ofReal_sum,apply_ite Complex.ofReal,Complex.ofReal_pow,Complex.ofReal_zero,f]

lemma wide_diagonal_mellin (σ : ℝ) (hσ : 0<σ) :
    Integrable (fun p : ℝ×ℝ => (experimentN:ℂ)^(line σ p.1+line σ p.2)*
      mellin (fun u => (wideCompanion u:ℂ)) (line σ p.1)*
      mellin (fun u => (wideCompanion u:ℂ)) (line σ p.2)*diagonalSeries experimentN (line σ p.1+line σ p.2)) ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z => (experimentN:ℂ)^(s+z)*
      mellin (fun u => (wideCompanion u:ℂ)) s*mellin (fun u => (wideCompanion u:ℂ)) z*
      diagonalSeries experimentN (s+z)))=(diagonalCountingMoment:ℂ) := by
  have hN : 0<experimentN := by norm_num [experimentN]
  obtain ⟨hi,hs⟩ := finite_double_mellin_inversion_series wideCompanion
    (wideCompanion_contDiff.of_le (by norm_num)) _ _ (wideCompanion_support.trans Ioo_subset_Icc_self) σ hσ
    (fun k : ℕ => (k+1:ℕ)/(experimentN:ℝ))
    (fun k : ℕ => if Nat.Coprime (k+1) experimentN then (mangoldt (k+1):ℂ)^2/(k+1:ℕ) else 0)
    (fun k => by positivity) (diagonal_mellin_coeff_summable experimentN hN σ hσ)
  have he (x y : ℝ) := diagonal_mellin_series experimentN hN wideWeight (line σ x) (line σ y)
    (by simp [line]; linarith)
  simp only [mellinWeight_wideWeight] at he
  constructor
  · exact hi.congr (Eventually.of_forall (fun p => he p.1 p.2))
  · rw [← wide_diagonal_tsum,hs.tsum_eq]
    unfold verticalMellin
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    exact (he x y).symm

end ConditionalGoldbach
