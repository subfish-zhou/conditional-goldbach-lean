import LiLiuGoldbach.EarlyAnalyticPrerequisites
import LiLiuGoldbach.ResidualMellinPrerequisites
import LiLiuGoldbach.Proofs.QuadraticFunctional
import LiLiuGoldbach.Proofs.MellinMoment
import LiLiuGoldbach.Proofs.HardyEvaluation

/-! Recovering the exact residual quadratic form using the adjoint and scalar Mellin integrals. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma ofReal_cpow_conj (u : ℝ) (hu : 0 < u) (s : ℂ) :
    (u : ℂ) ^ conj s = conj ((u : ℂ) ^ s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu.ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu.ne'), ← exp_conj, map_mul,
    ← ofReal_log hu.le, conj_ofReal]

lemma mellinWeight_conj (φ : ℝ → ℝ) (s : ℂ) :
    mellinWeight φ (conj s) = conj (mellinWeight φ s) := by
  unfold mellinWeight mellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [smul_eq_mul, map_mul, conj_ofReal]
  rw [← ofReal_cpow_conj u hu, map_sub, map_one]

lemma mellin_coefficient_conj (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ) (s : ℂ) :
    (N : ℂ) ^ conj s * mellinWeight φ (conj s) * (1 + conj s) =
      conj ((N : ℂ) ^ s * mellinWeight φ s * (1 + s)) := by
  rw [← ofReal_natCast, ofReal_cpow_conj (N : ℝ) (by exact_mod_cast hN), mellinWeight_conj]
  simp only [map_mul, map_add, map_one]

lemma line_conj (σ t : ℝ) : conj (line σ t) = line σ (-t) := by
  simp [line]

lemma verticalMellin_conj (σ : ℝ) (f : ℂ → ℂ) :
    conj (verticalMellin σ f) = verticalMellin σ (fun s => conj (f (conj s))) := by
  unfold verticalMellin
  simp only [map_mul, map_inv₀, map_ofNat, conj_ofReal, ← integral_conj, line_conj]
  congr 1
  exact (integral_neg_eq_self (fun t : ℝ => conj (f (line σ t))) volume).symm

lemma functional_kernel_recovery {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : σ ∈ Ioo a beta)
    (hstar : sigmaStar ∈ Ioo a beta) (T : HardySpace a beta →L[ℂ] HardySpace a beta)
    (K : ℂ → ℂ → ℂ)
    (hK : ∀ s z : ℂ, s ∈ strip a beta → z ∈ strip a beta →
      K s z = paperInner (T (evaluationVector z)) (evaluationVector s))
    (s : ℂ) (hs : s ∈ strip a beta) :
    fourierLaplace (T (rieszVector N φ)) s =
      verticalMellin σ (fun z =>
        (N : ℂ) ^ z * mellinWeight φ z * (1 + z) * K s (conj z)) := by
  have hv := (rieszVector_density_spec N hN φ hφ hstar).1 σ hσ
  have hstart : fourierLaplace (T (rieszVector N φ)) s =
      conj (functionalValue N φ σ (T.adjoint (evaluationVector s))) := by
    rw [hv, evaluationVector_spec hs]
    unfold paperInner
    rw [inner_conj_symm]
    exact (T.adjoint_inner_left (rieszVector N φ) (evaluationVector s)).symm
  rw [hstart, functionalValue, verticalMellin_conj]
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let z := line σ t
  have hz : conj z ∈ strip a beta := by simpa [z, strip, line] using hσ
  change conj ((N : ℂ) ^ conj z * mellinWeight φ (conj z) * (1 + conj z) *
    fourierLaplace (T.adjoint (evaluationVector s)) (conj z)) = _
  rw [map_mul, mellin_coefficient_conj N hN φ z, conj_conj,
    evaluationVector_spec hz, hK s (conj z) hs hz]
  congr 1
  unfold paperInner
  rw [inner_conj_symm]
  exact T.adjoint_inner_left (evaluationVector (conj z)) (evaluationVector s)

lemma quadratic_residual_integral {a : ℝ} (N : ℕ) [NeZero N]
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : σ ∈ Ioo a beta) (hσ0 : 0 < σ)
    (hstar : sigmaStar ∈ Ioo a beta) (T : HardySpace a beta →L[ℂ] HardySpace a beta)
    (hK : ∀ s z : ℂ, s ∈ strip a beta → z ∈ strip a beta →
      weightedKernel N s z = paperInner (T (evaluationVector z)) (evaluationVector s)) :
    paperInner (T (rieszVector N φ)) (rieszVector N φ) = residualIntegral N φ σ := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hv := (rieszVector_density_spec N hN φ hφ hstar).1 σ hσ
  rw [← hv (T (rieszVector N φ))]
  unfold functionalValue residualIntegral
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let s := line σ t
  have hs : s ∈ strip a beta := by simpa [s, strip, line] using hσ
  change (N : ℂ) ^ s * mellinWeight φ s * (1 + s) * fourierLaplace (T (rieszVector N φ)) s = _
  rw [functional_kernel_recovery N hN φ hφ σ hσ hstar T (weightedKernel N) hK s hs]
  unfold verticalMellin
  rw [mul_left_comm _ ((2 * (Real.pi : ℂ))⁻¹), ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  let z := line σ y
  have hsz : 1 + s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s, line] at hr
    linarith
  have hzz : 1 + z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [z, line] at hr
    linarith
  change (N : ℂ) ^ s * mellinWeight φ s * (1 + s) *
      ((N : ℂ) ^ z * mellinWeight φ z * (1 + z) * weightedKernel N s (conj z)) = _
  simp only [weightedKernel, conj_conj]
  rw [cpow_add _ _ hNz]
  field_simp
  <;> ring

theorem theorem_7_1 (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (ha : alpha N < beta) :
    (weightMass φ * singularSeries N - goldbach N φ : ℝ) =
      paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) ∧
    |weightMass φ * singularSeries N - goldbach N φ| ≤
      normFunctional N φ (alpha N) * ‖residualOperator ha N‖ := by
  have hN4 := (large_parameters hlarge).1
  have hlog : 10 < Real.log N := by
    have h := Real.log_lt_log (Real.exp_pos 10) hlarge
    simpa using h
  have hσ : sigmaStar ∈ Ioo (alpha N) beta := by
    constructor
    · unfold sigmaStar alpha
      apply (div_lt_div_iff₀ (by linarith : 0 < Real.log N) (by norm_num : (0 : ℝ) < 9)).2
      linarith
    · norm_num [sigmaStar, beta]
  have hσ0 : 0 < sigmaStar := by norm_num [sigmaStar]
  have heq : (weightMass φ * singularSeries N - goldbach N φ : ℝ) =
      paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) := by
    rw [quadratic_residual_integral N φ hφ sigmaStar hσ hσ0 hσ (residualOperator ha N)
      (fun s z hs hz => proposition_5_4_kernel_pairing N hN hlarge hGRH ha s z hs hz)]
    exact (proposition_7_3 N hN hN4 hGRH φ hφ sigmaStar hσ0 (by norm_num [sigmaStar])).symm
  refine ⟨heq, ?_⟩
  have hn := ((proposition_7_4 φ hφ).1 N hN hlarge).2.1
  have hbound : ‖paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ)‖ ≤
      ‖(rieszVector N φ : HardySpace (alpha N) beta)‖ ^ 2 * ‖residualOperator ha N‖ := by
    unfold paperInner
    calc
      _ ≤ ‖(rieszVector N φ : HardySpace (alpha N) beta)‖ *
          ‖residualOperator ha N (rieszVector N φ)‖ := norm_inner_le_norm _ _
      _ ≤ ‖(rieszVector N φ : HardySpace (alpha N) beta)‖ *
          (‖residualOperator ha N‖ * ‖(rieszVector N φ : HardySpace (alpha N) beta)‖) :=
        mul_le_mul_of_nonneg_left ((residualOperator ha N).le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  rw [← heq, Complex.norm_real, Real.norm_eq_abs, hn] at hbound
  exact hbound

end LiLiuGoldbach16
