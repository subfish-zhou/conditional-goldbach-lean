module

public import ConditionalGoldbach.Proofs.FiniteModelBasic
public import ConditionalGoldbach.Proofs.MellinModelBound

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach.FiniteModel

lemma mellinWeight_first_moment_integrable (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ) (σ : ℝ) (hσ : 0<σ) :
    Integrable (fun t : ℝ => (1+|t|) * ‖mellinWeight φ (line σ t)‖) := by
  obtain ⟨C,hC,hdec⟩ := mellinWeight_uniform_decay φ hφ σ σ hσ (le_refl σ)
  have hi : Integrable (fun t : ℝ => (1+|t|)⁻¹ ^ 2) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
    convert h using 1
    ext t
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]
  have hcont : Continuous (fun t : ℝ => mellinWeight φ (line σ t)) :=
    (mellinWeight_differentiable hφ).continuous.comp (by unfold line; fun_prop)
  apply (hi.const_mul C).mono' ((show Continuous (fun t : ℝ => 1+|t|) by fun_prop).mul hcont.norm).aestronglyMeasurable
  filter_upwards [] with t
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
  have hp : 0 < 1+|t| := by positivity
  have ht := hdec σ ⟨le_rfl,le_rfl⟩ t
  have hm := mul_le_mul_of_nonneg_left ht hp.le
  have hinv : 0 ≤ (1+|t|)⁻¹ := inv_nonneg.mpr hp.le
  have hinv1 : (1+|t|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg t])
  have hpow := pow_le_pow_of_le_one hinv hinv1 (show 2 ≤ 5 by norm_num)
  have he : (1+|t|) * (C*(1+|t|)⁻¹ ^ 6) = C*(1+|t|)⁻¹ ^ 5 := by field_simp
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hpow hC.le)

lemma model_double_integrable (N : ℕ) (φ : ℝ → ℝ) (hφ : FiniteModelWeight φ)
    (σ : ℝ) (hσ : 0 < σ) (hσupper : σ ≤ 1/9) :
    Integrable (fun p : ℝ × ℝ =>
      mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        continuedDensity N (line σ p.1 + line σ p.2) * betaKernel (line σ p.1) (line σ p.2)) := by
  obtain ⟨D,hD,hDb⟩ := continuedDensity_line_growth N (2*σ) (by linarith) (by linarith)
  let B : ℝ := ‖2 * betaIntegral (1/2-(σ : ℂ)) (2*σ) + betaIntegral (1/2-(σ : ℂ)) (1/2-(σ : ℂ))‖
  have hM : Continuous (fun t : ℝ => mellinWeight φ (line σ t)) :=
    (mellinWeight_differentiable hφ).continuous.comp (by unfold line; fun_prop)
  have hDcont := continuedDensity_line_continuous N (2*σ) (by linarith) (by linarith)
  have hline (v y : ℝ) : line σ v + line σ y = line (2*σ) (v+y) := by
    unfold line
    push_cast
    ring
  have hbm : Measurable (fun p : ℝ × ℝ => betaKernel (line σ p.1) (line σ p.2)) := by
    unfold betaKernel
    exact ((measurable_betaIntegral _ _ (by unfold line; fun_prop) (by unfold line; fun_prop)).add
      (measurable_betaIntegral _ _ (by unfold line; fun_prop) (by unfold line; fun_prop))).sub
        (measurable_betaIntegral _ _ (by unfold line; fun_prop) (by unfold line; fun_prop))
  have hm : Measurable (fun p : ℝ × ℝ => mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
      continuedDensity N (line σ p.1 + line σ p.2) * betaKernel (line σ p.1) (line σ p.2)) := by
    simp_rw [hline]
    exact (((hM.measurable.comp measurable_fst).mul (hM.measurable.comp measurable_snd)).mul
      (hDcont.measurable.comp (by fun_prop))).mul hbm
  rw [Measure.volume_eq_prod]
  apply (((mellinWeight_first_moment_integrable φ hφ σ hσ).mul_prod
    (mellinWeight_first_moment_integrable φ hφ σ hσ)).const_mul (D*B)).mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  rcases p with ⟨v,y⟩
  simp only [norm_mul]
  have hb : ‖betaKernel (line σ v) (line σ y)‖ ≤ B :=
    betaKernel_vertical_bound _ _ σ (by simp [line]) (by simp [line])
  have hd : ‖continuedDensity N (line σ v + line σ y)‖ ≤ D*(1+|v+y|) := by rw [hline]; exact hDb _
  have hadd : 1+|v+y| ≤ (1+|v|)*(1+|y|) := by
    nlinarith [abs_add_le v y, mul_nonneg (abs_nonneg v) (abs_nonneg y)]
  calc
    _ ≤ (‖mellinWeight φ (line σ v)‖ * ‖mellinWeight φ (line σ y)‖) * (D*(1+|v+y|)) * B := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hd (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hb
        (norm_nonneg _) (by positivity)
    _ ≤ (‖mellinWeight φ (line σ v)‖ * ‖mellinWeight φ (line σ y)‖) *
        (D*((1+|v|)*(1+|y|))) * B := by gcongr
    _ = _ := by ring

end ConditionalGoldbach.FiniteModel
