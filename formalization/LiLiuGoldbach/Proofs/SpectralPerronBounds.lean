import LiLiuGoldbach.Proofs.SpectralPoisson
import LiLiuGoldbach.Proofs.CharacterZeroSummability
import LiLiuGoldbach.Proofs.Elementary

/-! Quantitative residue bounds and the reference-line absorption for the smoothed Perron kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

def perronZeroCoefficient (X σ : ℝ) : ℝ :=
  ((Real.sqrt X)^(-σ) + X^(-σ)) / (σ * Real.log (Real.sqrt X))

lemma perronZeroCoefficient_nonneg {X σ : ℝ} (hX : 1 < X) (hσ : 0 < σ) :
    0 ≤ perronZeroCoefficient X σ := by
  have hxs : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
  unfold perronZeroCoefficient
  exact div_nonneg (add_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    (Real.rpow_nonneg (by linarith) _)) (mul_nonneg hσ.le (Real.log_pos hxs).le)

lemma smoothedPerronKernel_zero_bound {X σ t : ℝ} (hX : 1 < X) (hσ : 0 < σ)
    (ρ : ℂ) (hρ : ρ.re = 1 / 2) :
    ‖smoothedPerronKernel X (ρ - (1 / 2 + line σ t))‖ ≤
      perronZeroCoefficient X σ * (σ / (σ^2 + (t - ρ.im)^2)) := by
  have hXp : 0 < X := by linarith
  have hxs : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hX)
  have hxlog : 0 < Real.log (Real.sqrt X) := Real.log_pos hxs
  have hre : (ρ - (1 / 2 + line σ t)).re = -σ := by simp [line, hρ]
  have hnorm : ‖ρ - (1 / 2 + line σ t)‖^2 = σ^2 + (t - ρ.im)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [hre]
    simp [line]
    ring
  unfold smoothedPerronKernel
  rw [norm_div, norm_mul, norm_pow, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxlog]
  calc
    _ ≤ (X^(-σ) + (Real.sqrt X)^(-σ)) /
        ((σ^2 + (t - ρ.im)^2) * Real.log (Real.sqrt X)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (norm_sub_le _ _).trans_eq
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hXp,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Real.sqrt X), hre]
    _ = _ := by
      unfold perronZeroCoefficient
      field_simp
      ring

attribute [local instance] conductorNeZero in
lemma smoothedPerron_nontrivial_zero_sum_bound {N : ℕ} [NeZero N]
    (hGRH : GRH N) (χ : Character N) (hχ : χ ≠ 1)
    {X σ t : ℝ} (hX : 1 < X) (hσ : 0 < σ) :
    Summable (fun p : ZeroIndex χ.primitiveCharacter =>
      ‖smoothedPerronKernel X (p.val.1 - (1 / 2 + line σ t))‖) ∧
    ‖∑' p : ZeroIndex χ.primitiveCharacter,
      smoothedPerronKernel X (p.val.1 - (1 / 2 + line σ t))‖ ≤
      perronZeroCoefficient X σ * zeroPoisson χ σ t := by
  have hnon := primitiveCharacter_ne_one_of_ne_one χ hχ
  have hs := (primitive_zero_poisson_summable χ.primitiveCharacter hnon
    χ.primitiveCharacter_isPrimitive σ t hσ).mul_left (perronZeroCoefficient X σ)
  have hbound (p : ZeroIndex χ.primitiveCharacter) :
      ‖smoothedPerronKernel X (p.val.1 - (1 / 2 + line σ t))‖ ≤
        perronZeroCoefficient X σ * (σ / (σ^2 + (t - p.val.1.im)^2)) := by
    apply smoothedPerronKernel_zero_bound hX hσ
    exact hGRH χ.conductor inferInstance χ.conductor_dvd_level χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive p.val.1 p.property.1 p.property.2.1 p.property.2.2.1
  have hn := hs.of_nonneg_of_le (fun p => norm_nonneg _) hbound
  refine ⟨hn, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  calc
    _ ≤ ∑' p : ZeroIndex χ.primitiveCharacter,
        perronZeroCoefficient X σ * (σ / (σ^2 + (t - p.val.1.im)^2)) := hn.tsum_le_tsum hbound hs
    _ = _ := by rw [tsum_mul_left]; rfl

lemma perron_exponential_coefficient_lt {a : ℝ} (ha : 9 / 10 ≤ a) :
    (Real.exp (-a) + Real.exp (-2 * a)) / a < 2 / 3 := by
  have ha0 : 0 < a := by linarith
  have he : (12 / 5 : ℝ) ≤ Real.exp (9 / 10) := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10) 4
    norm_num [Finset.sum_range_succ] at hh
    linarith
  have hfirst : Real.exp (-a) ≤ 5 / 12 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos a)]
    have hh := he.trans (Real.exp_le_exp.mpr ha)
    nlinarith
  have hsecond : Real.exp (-2 * a) ≤ 25 / 144 := by
    rw [show -2 * a = -a + -a by ring, Real.exp_add]
    nlinarith [Real.exp_pos (-a)]
  apply (div_lt_iff₀ ha0).mpr
  linarith

lemma perron_reference_coefficient (N : ℕ) (hlarge : Real.exp 10 < (N : ℝ)) :
    0 ≤ perronZeroCoefficient ((N : ℝ) / 2) (referenceLine N) ∧
      perronZeroCoefficient ((N : ℝ) / 2) (referenceLine N) < 2 / 3 := by
  have hn : (0 : ℝ) < N := (Real.exp_pos 10).trans hlarge
  have hlog : 10 < Real.log N := (Real.lt_log_iff_exp_lt hn).mpr hlarge
  have hN4 : (4 : ℝ) < N := by
    have hh : (4 : ℝ) < Real.exp 10 := by
      have := Real.add_one_le_exp 10
      linarith
    linarith
  have hX : 1 < (N : ℝ) / 2 := by linarith
  have hσ : 0 < referenceLine N := by unfold referenceLine; positivity
  refine ⟨perronZeroCoefficient_nonneg hX hσ, ?_⟩
  let a := (referenceLine N) * Real.log (Real.sqrt ((N : ℝ) / 2))
  have ha : 9 / 10 ≤ a := by
    have hlog2 : Real.log (2 : ℝ) < 1 := by
      apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
      have hh := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      norm_num at hh
      linarith
    have he : a = 1 - Real.log 2 / Real.log N := by
      dsimp [a, referenceLine]
      rw [Real.log_sqrt (by positivity), Real.log_div hn.ne' (by norm_num)]
      field_simp
    rw [he]
    have hh : Real.log 2 / Real.log N ≤ 1 / 10 := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    linarith
  have he : perronZeroCoefficient ((N : ℝ) / 2) (referenceLine N) =
      (Real.exp (-a) + Real.exp (-2 * a)) / a := by
    unfold perronZeroCoefficient
    rw [Real.rpow_def_of_pos (Real.sqrt_pos.mpr (by positivity)), Real.rpow_def_of_pos (by positivity)]
    congr 2
    · congr 1
      dsimp [a]
      ring
    · congr 1
      dsimp [a]
      rw [Real.log_sqrt (by positivity)]
      ring
  rw [he]
  exact perron_exponential_coefficient_lt ha

lemma perron_absorb {g P : ℂ} {Q E ε C₁ C₂ : ℝ} (hE : 0 ≤ E)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 2 / 3) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (htrunc : ‖-g - P‖ ≤ ε * Q + C₁ * E) (hQ : Q ≤ ‖g‖ + C₂ * E) :
    ‖g‖ ≤ 3 * (‖P‖ + (C₁ + C₂) * E) := by
  have htriangle : ‖g‖ ≤ ‖-g - P‖ + ‖P‖ := by
    have hh := norm_add_le (-g - P) P
    simpa only [sub_add_cancel, norm_neg] using hh
  have hQ' := mul_le_mul_of_nonneg_left hQ hε0
  have hC := mul_nonneg hC₂ hE
  have heC : ε * (C₂ * E) ≤ C₂ * E := by nlinarith
  have heg := mul_le_mul_of_nonneg_right hε (norm_nonneg g)
  nlinarith

/-- Once the analytic smoothed truncation and Poisson comparison are established,
this is the uniform absorption step at the paper's exact reference line. -/
lemma reference_logDerivative_bound_of_smoothed_truncation
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (N : ℕ) [NeZero N] (hlarge : Real.exp 10 < (N : ℝ)) (χ : Character N) (t : ℝ)
    (htrunc : ‖-logDerivative χ (line (referenceLine N) t) -
        smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line (referenceLine N) t)‖ ≤
      perronZeroCoefficient ((N : ℝ) / 2) (referenceLine N) * zeroPoisson χ (referenceLine N) t +
        C₁ * Real.log (N * (|t| + 2)))
    (hQ : |zeroPoisson χ (referenceLine N) t - (logDerivative χ (line (referenceLine N) t)).re| ≤
      C₂ * Real.log (N * (|t| + 2))) :
    ‖logDerivative χ (line (referenceLine N) t)‖ ≤
      (3 * (1 + C₁ + C₂)) *
        (‖smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line (referenceLine N) t)‖ +
          Real.log (N * (|t| + 2))) := by
  have hN1 : (1 : ℝ) < N := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 10)).trans hlarge
  have hE : 0 ≤ Real.log (N * (|t| + 2)) := Real.log_nonneg (by nlinarith [abs_nonneg t])
  have hε := perron_reference_coefficient N hlarge
  have hQ' : zeroPoisson χ (referenceLine N) t ≤ ‖logDerivative χ (line (referenceLine N) t)‖ +
      C₂ * Real.log (N * (|t| + 2)) := by
    have hh := (abs_le.mp hQ).2
    have hr := Complex.re_le_norm (logDerivative χ (line (referenceLine N) t))
    linarith
  have hb := perron_absorb hE hε.1 hε.2.le hC₁ hC₂ htrunc hQ'
  apply hb.trans
  have hP := norm_nonneg (smoothedDirichletPolynomial χ ((N : ℝ) / 2) (1 / 2 + line (referenceLine N) t))
  nlinarith [mul_nonneg (add_nonneg hC₁ hC₂) hP]

end LiLiuGoldbach16
