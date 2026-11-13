import LiLiuGoldbach.ModelMellinPrerequisites
import LiLiuGoldbach.Proofs.MellinDiagonal
import LiLiuGoldbach.Proofs.MellinCharacterShift
import LiLiuGoldbach.Proofs.ModelContinuation

/-! The arithmetic residual, with the signs of all three Mellin terms retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma double_verticalMellin_sub (σ : ℝ) (f g : ℂ → ℂ → ℂ)
    (hf : Integrable (fun p : ℝ × ℝ => f (line σ p.1) (line σ p.2)))
    (hg : Integrable (fun p : ℝ × ℝ => g (line σ p.1) (line σ p.2))) :
    verticalMellin σ (fun s => verticalMellin σ (fun z => f s z - g s z)) =
      verticalMellin σ (fun s => verticalMellin σ (f s)) -
        verticalMellin σ (fun s => verticalMellin σ (g s)) := by
  simp only [verticalMellin, integral_const_mul]
  rw [integral_integral_sub hf hg]
  ring

lemma weighted_continuedModel_cancel (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ)
    (s z : ℂ) (hd : (s, z) ∈ betaDomain) :
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * continuedModel N s z =
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s + z) * betaKernel s z := by
  rw [← betaModel_eq_continuedModel N hN s z hd, betaModel, cpow_neg]
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNp : (N : ℂ) ^ (s + z) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hNz)
  field_simp

lemma mellin_betaDomain_line (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) (x y : ℝ) :
    (line σ x, line σ y) ∈ betaDomain := by
  simp only [betaDomain, mem_setOf_eq, line, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
  constructor
  · linarith
  constructor <;> linarith

lemma residual_mellin_split (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) * mellinWeight φ (line σ p.1) *
        mellinWeight φ (line σ p.2) * residual N (line σ p.1) (line σ p.2)) ∧
    residualIntegral N φ σ = (characterMoment N φ : ℂ) - diagonalMoment N φ +
      (weightMass φ * singularSeries N : ℝ) := by
  let P : ℂ → ℂ → ℂ := fun s z =>
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * characterKernel N s z
  let D : ℂ → ℂ → ℂ := fun s z =>
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * diagonalSeries N (s + z)
  let K : ℂ → ℂ → ℂ := fun s z =>
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * continuedModel N s z
  have hNpos : 0 < N := by omega
  have hcancel (x y : ℝ) := weighted_continuedModel_cancel N hNpos φ
    (line σ x) (line σ y) (mellin_betaDomain_line σ hσ hσ' x y)
  obtain ⟨hPi, hPv⟩ := characterMoment_mellin_shifted N hN hN4 hGRH φ hφ σ hσ (by linarith)
  obtain ⟨hDi, hDv⟩ := diagonalMoment_mellin N hNpos φ hφ σ hσ
  have hKi' := (lemma_7_2_absolute_convergence N hN hN4 φ hφ σ hσ hσ').2
  have hKi : Integrable (fun p : ℝ × ℝ => K (line σ p.1) (line σ p.2)) := by
    apply hKi'.congr
    filter_upwards [] with p
    exact (hcancel p.1 p.2).symm
  have hsplit (s z : ℂ) :
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * residual N s z =
        (P s z - D s z) - K s z := by dsimp [P, D, K, residual]; ring
  constructor
  · simp_rw [hsplit]
    exact (hPi.sub hDi).sub hKi
  · unfold residualIntegral
    simp_rw [hsplit]
    rw [double_verticalMellin_sub σ _ K (hPi.sub hDi) hKi,
      double_verticalMellin_sub σ P D hPi hDi, ← hPv,
      hDv]
    have hKval : verticalMellin σ (fun s => verticalMellin σ (K s)) =
        -(weightMass φ * singularSeries N : ℝ) := by
      rw [← (lemma_7_2 N hN hN4 φ hφ σ hσ hσ').2]
      unfold verticalMellin
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      exact hcancel x y
    rw [hKval]
    ring

theorem proposition_7_3 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ)
    (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    residualIntegral N φ σ = (weightMass φ * singularSeries N - goldbach N φ : ℝ) := by
  rw [(residual_mellin_split N hN hN4 hGRH φ hφ σ hσ hσ').2,
    goldbach_eq_diagonal_sub_character N hN hN4 φ hφ]
  push_cast
  ring

theorem proposition_7_3_absolute_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        residual N (line σ p.1) (line σ p.2)) :=
  (residual_mellin_split N hN hN4 hGRH φ hφ σ hσ hσ').1

end LiLiuGoldbach16
