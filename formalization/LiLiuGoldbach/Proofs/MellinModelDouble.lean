import LiLiuGoldbach.Proofs.MellinBetaRelation
import LiLiuGoldbach.Proofs.MellinModelBound
import LiLiuGoldbach.Proofs.MellinDiagonal
import LiLiuGoldbach.Proofs.MellinMoment

/-! The complete original Lemma 7.2: diagonal and signed model inversion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma double_verticalMellin_diagonal (F : ℂ → ℂ → ℂ) (σ : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => F (line σ p.1) (line σ p.2))) :
    verticalMellin σ (fun s => verticalMellin σ (fun z => F s z)) =
      verticalMellin (2*σ) (fun w => verticalMellin σ (fun s => F s (w-s))) := by
  have hline (v t : ℝ) : line (2*σ) t-line σ v = line σ (t-v) := by
    unfold line
    push_cast
    ring
  rw [Measure.volume_eq_prod] at hi
  have hg : Integrable (fun p : ℝ × ℝ => F (line σ p.1) (line σ (p.2-p.1)))
      (volume.prod volume) := (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable hi
  have he : (∫ v : ℝ, ∫ y : ℝ, F (line σ v) (line σ y)) =
      ∫ t : ℝ, ∫ v : ℝ, F (line σ v) (line (2*σ) t-line σ v) := by
    calc
      _ = ∫ v : ℝ, ∫ t : ℝ, F (line σ v) (line σ (t-v)) := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact (integral_sub_right_eq_self (μ := volume) (fun y : ℝ => F (line σ v) (line σ y)) v).symm
      _ = ∫ t : ℝ, ∫ v : ℝ, F (line σ v) (line σ (t-v)) :=
        integral_integral_swap (f := fun v t : ℝ => F (line σ v) (line σ (t-v))) hg
      _ = _ := by simp_rw [hline]
  simp only [verticalMellin, integral_const_mul, he]

lemma model_double_mellin (N : ℕ) (hN : Even N) (hpos : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s+z) * betaKernel s z)) =
        -(weightMass φ * singularSeries N : ℝ) := by
  rw [double_verticalMellin_diagonal _ σ (model_double_integrable N φ hφ σ hσ hσupper)]
  rw [← (model_single_mellin N hN hpos φ hφ (2*σ) (by linarith)).2]
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let w := line (2*σ) t
  have hw : w.re = 2*σ := by simp [w,line]
  have hbeta := (signedConvolution_mellin_beta φ hφ σ hσ hσupper w hw).2
  have he (s : ℂ) : mellinWeight φ s * mellinWeight φ (w-s) *
      continuedDensity N (s+(w-s)) * betaKernel s (w-s) =
      continuedDensity N w * (mellinWeight φ s * mellinWeight φ (w-s) * betaKernel s (w-s)) := by
    rw [add_sub_cancel]
    ring
  change (2*(Real.pi : ℂ))⁻¹ *
    (∫ u : ℝ, mellinWeight φ (line σ u) * mellinWeight φ (w-line σ u) *
      continuedDensity N (line σ u+(w-line σ u)) * betaKernel (line σ u) (w-line σ u)) = _
  simp_rw [he]
  rw [integral_const_mul]
  change (2*(Real.pi : ℂ))⁻¹ * (continuedDensity N w * _) =
    continuedDensity N w * mellin (fun y => (signedConvolution φ y : ℂ)) w
  rw [hbeta]
  unfold verticalMellin
  ring

theorem lemma_7_2 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * diagonalSeries N (s + z))) =
        diagonalMoment N φ ∧
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s + z) * betaKernel s z)) =
        -(weightMass φ * singularSeries N : ℝ) := by
  exact ⟨(diagonalMoment_mellin N (by omega) φ hφ σ hσ).2,
    model_double_mellin N hN (by omega) φ hφ σ hσ hσ'⟩

theorem lemma_7_2_absolute_convergence (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / 9) :
    Integrable (fun p : ℝ × ℝ =>
      (N : ℂ) ^ (line σ p.1 + line σ p.2) *
        mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        diagonalSeries N (line σ p.1 + line σ p.2)) ∧
    Integrable (fun p : ℝ × ℝ =>
      mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        continuedDensity N (line σ p.1 + line σ p.2) *
        betaKernel (line σ p.1) (line σ p.2)) := by
  exact ⟨(diagonalMoment_mellin N (by omega) φ hφ σ hσ).1,
    model_double_integrable N φ hφ σ hσ hσ'⟩

end LiLiuGoldbach16
