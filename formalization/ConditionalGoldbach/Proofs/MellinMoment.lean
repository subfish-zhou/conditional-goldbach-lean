module

public import ConditionalGoldbach.Proofs.MellinProjection
public import ConditionalGoldbach.Proofs.CharacterAnalytic
public import ConditionalGoldbach.Proofs.SignedFamilies

/-! The initial double Mellin projection of the odd-character moment. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma verticalMellin_const_mul (σ : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    verticalMellin σ (fun z => c * f z) = c * verticalMellin σ f := by
  simp only [verticalMellin, integral_const_mul]
  ring

lemma verticalMellin_mul_const (σ : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    verticalMellin σ (fun z => f z * c) = verticalMellin σ f * c := by
  simp only [verticalMellin, integral_mul_const]
  ring

lemma verticalMellin_finset_sum {ι : Type*} (S : Finset ι) (σ : ℝ) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, Integrable (fun t : ℝ => f i (line σ t))) :
    verticalMellin σ (fun z => ∑ i ∈ S, f i z) = ∑ i ∈ S, verticalMellin σ (f i) := by
  simp only [verticalMellin, integral_finsetSum S hf, Finset.mul_sum]

lemma double_verticalMellin_finset_prod {ι : Type*} (S : Finset ι)
    (σ : ℝ) (c : ℂ) (f g : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, Integrable (fun t : ℝ => f i (line σ t)))
    (hg : ∀ i ∈ S, Integrable (fun t : ℝ => g i (line σ t))) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      c * ∑ i ∈ S, f i s * g i z)) =
      c * ∑ i ∈ S, verticalMellin σ (f i) * verticalMellin σ (g i) := by
  have hi (s : ℂ) : verticalMellin σ (fun z => c * ∑ i ∈ S, f i s * g i z) =
      c * ∑ i ∈ S, f i s * verticalMellin σ (g i) := by
    rw [verticalMellin_const_mul, verticalMellin_finset_sum S σ _
      (fun i hi => (hg i hi).const_mul (f i s))]
    simp_rw [verticalMellin_const_mul]
  simp_rw [hi]
  rw [verticalMellin_const_mul, verticalMellin_finset_sum S σ _
    (fun i hi => (hf i hi).mul_const (verticalMellin σ (g i)))]
  simp_rw [verticalMellin_mul_const]

lemma characterPolynomial_star (N : ℕ) (χ : Character N) (φ : ℝ → ℝ) :
    characterPolynomial (star χ) φ = conj (characterPolynomial χ φ) := by
  simp only [characterPolynomial, map_mul, map_inv₀, map_sum,
    Complex.conj_ofReal, MulChar.star_apply, RCLike.star_def]

lemma weighted_characterKernel_factor (N : ℕ) [NeZero N] (φ : ℝ → ℝ) (s z : ℂ) :
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z =
      (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N,
        ((N : ℂ) ^ s * mellinWeight φ s * logDerivative χ s) *
        ((N : ℂ) ^ z * mellinWeight φ z * logDerivative (star χ) z) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [characterKernel_eq_star_sum, cpow_add _ _ hN]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem characterMoment_mellin_initial (N : ℕ) [NeZero N]
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 1 / 2 < σ) :
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z)) := by
  simp_rw [weighted_characterKernel_factor]
  rw [double_verticalMellin_finset_prod (oddCharacters N) σ _ _ _
    (fun χ _ => character_mellin_initial_integrable χ φ hφ σ hσ)
    (fun χ _ => character_mellin_initial_integrable (star χ) φ hφ σ hσ)]
  unfold characterMoment
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  have hχ := characterPolynomial_mellin_initial χ φ hφ σ hσ
  have hχbar := characterPolynomial_mellin_initial (star χ) φ hφ σ hσ
  calc
    _ = characterPolynomial χ φ * characterPolynomial (star χ) φ := by
      rw [characterPolynomial_star, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    _ = _ := by rw [hχ, hχbar]; ring

theorem characterMoment_mellin_initial_integrable (N : ℕ) [NeZero N]
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 1 / 2 < σ) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) * mellinWeight φ (line σ p.1) *
        mellinWeight φ (line σ p.2) * characterKernel N (line σ p.1) (line σ p.2)) := by
  simp_rw [weighted_characterKernel_factor]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro χ _
  exact (character_mellin_initial_integrable χ φ hφ σ hσ).mul_prod
    (character_mellin_initial_integrable (star χ) φ hφ σ hσ)


theorem lemma_3_5 (N : ℕ) [NeZero N] (_hN : Even N) (_hN4 : 4 ≤ N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 1 / 2 < σ) :
    (characterMoment N φ : ℂ) = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z)) ∧
    ∀ n m : ℕ, 0 < n → 0 < m → n ≠ m →
      (((n : ZMod N) = m) ↔
        (∃ k : ℕ, 0 < k ∧ m = n + k * N) ∨ (∃ k : ℕ, 0 < k ∧ n = m + k * N)) ∧
      (((n : ZMod N) = -(m : ZMod N)) ↔ ∃ k : ℕ, 0 < k ∧ n + m = k * N) := by
  refine ⟨characterMoment_mellin_initial N φ hφ σ hσ, ?_⟩
  intro n m hn hm hnm
  exact ⟨difference_congruence_families N n m hnm, sum_congruence_family N n m hn hm⟩

end ConditionalGoldbach
