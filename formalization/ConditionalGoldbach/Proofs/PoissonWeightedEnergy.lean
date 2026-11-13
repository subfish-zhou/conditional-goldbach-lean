import ConditionalGoldbach.Proofs.HalfPlanePoisson
import ConditionalGoldbach.Proofs.CharacterHalfPlane

/-! Weighted Poisson contraction and its application to logarithmic-derivative energies. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma poisson_weighted_integral_bound (F : ℝ → ℝ) (hc : Continuous F)
    (hn : ∀ t, 0 ≤ F t) (hI : Integrable (fun t : ℝ => F t / (1+t^2)))
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Integrable (fun t : ℝ => (∫ v : ℝ, poissonKernelReal ℓ (t-v)*F v) / (1+t^2)) ∧
      (∫ t : ℝ, (∫ v : ℝ, poissonKernelReal ℓ (t-v)*F v) / (1+t^2)) ≤
        (1+ℓ) * (∫ v : ℝ, F v / (1+v^2)) := by
  let H (t v : ℝ) := poissonKernelReal ℓ (t-v)*F v / (1+t^2)
  have hH (t v : ℝ) : H t v = (Real.pi * F v) *
      (poissonKernelReal 1 t * poissonKernelReal ℓ (v-t)) := by
    dsimp [H,poissonKernelReal]
    rw [show (v-t)^2 = (t-v)^2 by ring]
    field_simp
  have hinner (v : ℝ) : Integrable (fun t : ℝ => H t v) ∧
      (∫ t : ℝ, H t v) = Real.pi * F v * poissonKernelReal (1+ℓ) v := by
    obtain ⟨hi,he,hb⟩ := lemma_6_4_poisson_convolution ℓ hℓ v
    constructor
    · exact (hi.const_mul _).congr (Eventually.of_forall (fun t => (hH t v).symm))
    · simp_rw [hH]
      rw [integral_const_mul]
      exact congrArg (fun r : ℝ => Real.pi*F v*r) he
  have hnon (t v : ℝ) : 0 ≤ H t v := by
    dsimp [H]
    exact div_nonneg (mul_nonneg (poissonKernelReal_bounds ℓ hℓ _).1 (hn v)) (by positivity)
  have hb (v : ℝ) : Real.pi*F v*poissonKernelReal (1+ℓ) v ≤ (1+ℓ)*(F v/(1+v^2)) := by
    have hh := mul_le_mul_of_nonneg_left (lemma_6_4_poisson_convolution ℓ hℓ v).2.2
      (mul_nonneg Real.pi_pos.le (hn v))
    convert hh using 1
    unfold poissonKernelReal
    field_simp
  have hj : Integrable (fun v : ℝ => Real.pi*F v*poissonKernelReal (1+ℓ) v) := by
    refine (hI.const_mul (1+ℓ)).mono' ?_ ?_
    · exact ((continuous_const.mul hc).mul (poissonKernelReal_continuous (1+ℓ) (by positivity))).aestronglyMeasurable
    · filter_upwards [] with v
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (mul_nonneg Real.pi_pos.le (hn v)) (poissonKernelReal_bounds (1+ℓ) (by positivity) v).1)]
      exact hb v
  have hprod : Integrable (Function.uncurry H) (volume.prod volume) := by
    apply (integrable_prod_iff' ?_).mpr
    · constructor
      · exact Eventually.of_forall (fun v => (hinner v).1)
      · apply hj.congr
        filter_upwards [] with v
        rw [← (hinner v).2]
        apply integral_congr_ae
        filter_upwards [] with t
        exact (Real.norm_of_nonneg (hnon t v)).symm
    · apply Continuous.aestronglyMeasurable
      change Continuous (fun p : ℝ×ℝ => poissonKernelReal ℓ (p.1-p.2)*F p.2 / (1+p.1^2))
      exact (((poissonKernelReal_continuous ℓ hℓ).comp (continuous_fst.sub continuous_snd)).mul
        (hc.comp continuous_snd)).div (by fun_prop) (by intro p; positivity)
  have he (t : ℝ) : (∫ v : ℝ, H t v) = (∫ v : ℝ, poissonKernelReal ℓ (t-v)*F v)/(1+t^2) := by
    exact integral_div _ _
  refine ⟨hprod.integral_prod_left.congr (Eventually.of_forall he), ?_⟩
  simp_rw [← he]
  rw [integral_integral_swap hprod]
  simp_rw [(hinner _).2]
  calc
    _ ≤ ∫ v : ℝ, (1+ℓ)*(F v/(1+v^2)) := integral_mono hj (hI.const_mul _) hb
    _ = _ := integral_const_mul _ _

lemma halfPlane_weighted_energy_shift (f : ℂ → ℂ)
    (hd : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ f z)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖f (line x t)‖ ≤ C * (1 + |t|) ^ (1/2 : ℝ))
    (hb : ∃ R₀ B : ℝ, ∀ z : ℂ, R₀ ≤ z.re → ‖f z‖ ≤ B)
    (hI : Integrable (fun t : ℝ => ‖f (line 0 t)‖ ^ 2 / (1+t^2)))
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Integrable (fun t : ℝ => ‖f (line ℓ t)‖ ^ 2 / (1+t^2)) ∧
      (∫ t : ℝ, ‖f (line ℓ t)‖ ^ 2 / (1+t^2)) ≤
        (1+ℓ) * (∫ t : ℝ, ‖f (line 0 t)‖ ^ 2 / (1+t^2)) := by
  have hc (x : ℝ) (hx : 0 ≤ x) : Continuous (fun t : ℝ => f (line x t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hd (line x t) (by simpa [line] using hx)).continuousAt.comp
      (show ContinuousAt (fun t : ℝ => line x t) t by unfold line; fun_prop)
  obtain ⟨hpi,hpe⟩ := poisson_weighted_integral_bound (fun t => ‖f (line 0 t)‖ ^ 2)
    ((hc 0 le_rfl).norm.pow 2) (fun t => sq_nonneg _) hI hℓ
  have hpoint (t : ℝ) : ‖f (line ℓ t)‖ ^ 2 / (1+t^2) ≤
      (∫ v : ℝ, poissonKernelReal ℓ (t-v)*‖f (line 0 v)‖ ^ 2)/(1+t^2) :=
    div_le_div_of_nonneg_right (halfPlane_poisson_square_bound f hd hg hb hI hℓ t).2 (by positivity)
  have hi : Integrable (fun t : ℝ => ‖f (line ℓ t)‖ ^ 2 / (1+t^2)) := by
    refine hpi.mono' (((hc ℓ hℓ.le).norm.pow 2).div (by fun_prop) (by intro t; positivity)).aestronglyMeasurable ?_
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖f (line ℓ t)‖ ^ 2 / (1+t^2))] using hpoint t
  exact ⟨hi, (integral_mono hi hpi hpoint).trans hpe⟩

lemma logDerivative_energy_shift (N : ℕ) [NeZero N] (hN4 : 4 ≤ N) (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (σ ℓ : ℝ) (hσ : 0 < σ) (hℓ : 0 ≤ ℓ) :
    (∫ t : ℝ, ‖logDerivative χ (line (σ+ℓ) t)‖ ^ 2 / (1+t^2)) ≤
      (1+ℓ) * (∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1+t^2)) := by
  rcases hℓ.eq_or_lt with rfl | hℓ
  · simp
  have hg := shifted_logDerivative_growth N hN4 hGRH χ hχ hσ
  have hg' : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 R, ∀ t : ℝ,
      ‖logDerivative χ ((σ : ℂ)+line x t)‖ ≤ C*(1+|t|)^(1/2 : ℝ) := by
    intro R hR
    obtain ⟨C,hC,hg⟩ := hg R hR
    refine ⟨C,hC,?_⟩
    intro x hx t
    exact (hg x hx t).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by nlinarith [abs_nonneg t] : 1 ≤ 1+|t|) (by norm_num : (1/4 : ℝ) ≤ 1/2)) hC)
  have he (x t : ℝ) : (σ : ℂ)+line x t = line (σ+x) t := by unfold line; push_cast; ring
  have hh := halfPlane_weighted_energy_shift (fun z => logDerivative χ ((σ : ℂ)+z))
    (shifted_logDerivative_holomorphic N hGRH χ hχ hσ) hg'
    (by
      refine ⟨1,3*(Real.log 4+4),?_⟩
      intro z hz
      exact logDerivative_right_bound N χ _ (by simp only [add_re,ofReal_re]; linarith))
    (by simpa only [he,add_zero] using logDerivative_weighted_square_integrable N hN4 hGRH χ hχ σ hσ) hℓ
  simpa only [he,add_zero] using hh.2

lemma averagedLogDerivative_shift (N : ℕ) [NeZero N] (hN4 : 4 ≤ N) (hGRH : GRH N)
    (σ ℓ : ℝ) (hσ : 0 < σ) (hℓ : 0 ≤ ℓ) :
    averagedLogDerivative N (σ+ℓ) ≤ (1+ℓ)*averagedLogDerivative N σ := by
  unfold averagedLogDerivative
  calc
    _ ≤ (2 / (N.totient : ℝ)) * ∑ χ ∈ oddCharacters N,
        (1+ℓ)*(∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1+t^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ hχ =>
        logDerivative_energy_shift N hN4 hGRH χ hχ σ ℓ hσ hℓ)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

end ConditionalGoldbach
