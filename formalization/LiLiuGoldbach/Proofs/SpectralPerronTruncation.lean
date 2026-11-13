import LiLiuGoldbach.Proofs.SpectralPerronFubini
import LiLiuGoldbach.Proofs.SpectralPerronBounds
import LiLiuGoldbach.Proofs.SpectralPerronEuler
import LiLiuGoldbach.Proofs.SpectralPerronSeries
import LiLiuGoldbach.Proofs.CharacterZeroExpansion

/-! Perron integration of the actual Hadamard zero expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] conductorNeZero

lemma completedL_ne_zero_of_GRH {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ≠ 1) {u : ℂ} (hu : 1/2 < u.re) :
    completedL χ.primitiveCharacter u ≠ 0 := by
  intro hz
  have hχp := primitiveCharacter_ne_one_of_ne_one χ hχ
  exact primitive_LFunction_ne_zero_of_GRH hGRH χ.conductor_dvd_level χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive hχp hu
    ((completedL_eq_zero_iff χ.primitiveCharacter hχp χ.primitiveCharacter_isPrimitive _).mp hz).2.2

lemma zeroDifference_sub {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (u v w : ℂ)
    (hu : completedL χ u ≠ 0) (hv : completedL χ v ≠ 0) (hw : completedL χ w ≠ 0) :
    zeroDifference χ u w - zeroDifference χ v w = zeroDifference χ u v := by
  unfold zeroDifference
  rw [← (primitive_zero_difference_summable_norm χ hχ hprim u w hu hw).of_norm.tsum_sub
    (primitive_zero_difference_summable_norm χ hχ hprim v w hv hw).of_norm]
  apply tsum_congr
  intro p
  ring

lemma logDerivative_difference_zero_expansion {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (s v : ℂ)
    (hs : 0 < s.re) (hsv : 0 < (s+v).re) :
    logDerivative χ (s+v) - logDerivative χ s =
      zeroDifference χ.primitiveCharacter (1/2+s+v) (1/2+s) -
      (logDeriv Gamma ((1/2+s+v+1)/2) - logDeriv Gamma ((1/2+s+1)/2))/2 +
      (eulerCorrection χ (1/2+s+v)-eulerCorrection χ (1/2+s)) := by
  have hχn := odd_character_ne_one χ (Finset.mem_filter.mp hχ).2
  have hχp := primitiveCharacter_ne_one_of_ne_one χ hχn
  have h₁ := logDerivative_zero_expansion hGRH χ hχ (s+v) hsv
  have h₂ := logDerivative_zero_expansion hGRH χ hχ s hs
  have h₃ := zeroDifference_sub χ.primitiveCharacter hχp χ.primitiveCharacter_isPrimitive
    (1/2+(s+v)) (1/2+s) 2
    (completedL_ne_zero_of_GRH hGRH χ hχn (by norm_num; exact hsv))
    (completedL_ne_zero_of_GRH hGRH χ hχn (by norm_num; exact hs))
    (completedL_ne_zero_of_GRH hGRH χ hχn (by norm_num))
  rw [show (1/2+(s+v) : ℂ) = 1/2+s+v by ring] at h₁ h₃
  rw [show ((1/2+s+v+1)/2 : ℂ) = 3/4+(s+v)/2 by ring,
    show ((1/2+s+1)/2 : ℂ) = 3/4+s/2 by ring]
  simp only [logDeriv, Pi.div_apply]
  linear_combination h₁-h₂+h₃

lemma perron_zeroDifference_integral {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ≠ 1) {X c σ : ℝ}
    (hX : 1 < X) (hc : 0 < c) (hσ : 0 < σ) (t : ℝ) :
    Integrable (fun τ : ℝ => smoothedPerronKernel X (line c (2 * Real.pi * τ)) *
      zeroDifference χ.primitiveCharacter (1/2+line σ t+line c (2 * Real.pi * τ)) (1/2+line σ t)) ∧
    (∫ τ : ℝ, smoothedPerronKernel X (line c (2 * Real.pi * τ)) *
      zeroDifference χ.primitiveCharacter (1/2+line σ t+line c (2 * Real.pi * τ)) (1/2+line σ t)) =
      ∑' p : ZeroIndex χ.primitiveCharacter,
        smoothedPerronKernel X (p.val.1-(1/2+line σ t)) := by
  let δ := fun p : ZeroIndex χ.primitiveCharacter => (t-p.val.1.im)/(2*Real.pi)
  have hs := primitive_zero_shift_five_quarters_summable χ.primitiveCharacter
    (primitiveCharacter_ne_one_of_ne_one χ hχ) χ.primitiveCharacter_isPrimitive t
  letI : Countable (ZeroIndex χ.primitiveCharacter) := by
    apply Set.countable_univ_iff.mp
    convert hs.countable_support using 1
    ext p
    simp [Function.mem_support, ne_of_gt (Real.rpow_pos_of_pos
      (by positivity : 0 < 1 + |(t-p.val.1.im)/(2*Real.pi)|) (-(5/4 : ℝ)))]
  have hh := perron_resolvent_sum_integral hX hc hσ δ hs
  have ha (p : ZeroIndex χ.primitiveCharacter) :
      1/2+line σ t-p.val.1 = line σ (2*Real.pi*δ p) := by
    have hre := hGRH χ.conductor inferInstance χ.conductor_dvd_level χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive p.val.1 p.property.1 p.property.2.1 p.property.2.2.1
    apply Complex.ext
    · simp [line,hre]
    · have hd : 2*Real.pi*δ p = t-p.val.1.im := by
        dsimp [δ]
        field_simp
      simpa only [sub_im, add_im, show (1/2 : ℂ).im = 0 by norm_num,
        line, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] using hd.symm
  have he (τ : ℝ) : smoothedPerronKernel X (line c (2 * Real.pi * τ)) *
      zeroDifference χ.primitiveCharacter (1/2+line σ t+line c (2 * Real.pi * τ)) (1/2+line σ t) =
      ∑' p : ZeroIndex χ.primitiveCharacter,
        smoothedPerronKernel X (line c (2 * Real.pi * τ)) *
        ((line c (2 * Real.pi * τ) + line σ (2 * Real.pi * δ p))⁻¹ -
          (line σ (2 * Real.pi * δ p))⁻¹) := by
    unfold zeroDifference
    rw [tsum_mul_left]
    congr 1
    apply tsum_congr
    intro p
    rw [show 1/2+line σ t+line c (2*Real.pi*τ)-p.val.1 =
      line c (2*Real.pi*τ)+(1/2+line σ t-p.val.1) by ring,ha p]
    simp [one_div]
  simp_rw [he]
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply tsum_congr
  intro p
  congr 1
  rw [← ha p]
  ring

lemma smoothed_truncation_bound_of_gamma_integral {N : ℕ} [NeZero N]
    (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    {X σ : ℝ} (hX : 1 < X) (hσ : 0 < σ) (t C : ℝ)
    (hGi : Integrable (fun τ : ℝ => smoothedPerronKernel X (line 1 (2*Real.pi*τ)) *
      ((logDeriv Gamma ((1/2+line σ t+line 1 (2*Real.pi*τ)+1)/2) -
        logDeriv Gamma ((1/2+line σ t+1)/2))/2)))
    (hGb : ‖∫ τ : ℝ, smoothedPerronKernel X (line 1 (2*Real.pi*τ)) *
      ((logDeriv Gamma ((1/2+line σ t+line 1 (2*Real.pi*τ)+1)/2) -
        logDeriv Gamma ((1/2+line σ t+1)/2))/2)‖ ≤ C) :
    ‖-logDerivative χ (line σ t) - smoothedDirichletPolynomial χ X (1/2+line σ t)‖ ≤
      perronZeroCoefficient X σ * zeroPoisson χ σ t + C + 8*Real.log N := by
  let s := line σ t
  let v : ℝ → ℂ := fun τ => line 1 (2*Real.pi*τ)
  let K : ℝ → ℂ := fun τ => smoothedPerronKernel X (v τ)
  let Z : ℝ → ℂ := fun τ => zeroDifference χ.primitiveCharacter (1/2+s+v τ) (1/2+s)
  let G : ℝ → ℂ := fun τ =>
    (logDeriv Gamma ((1/2+s+v τ+1)/2)-logDeriv Gamma ((1/2+s+1)/2))/2
  let E : ℝ → ℂ := fun τ => eulerCorrection χ (1/2+s+v τ)
  have hu : 1/2 ≤ (1/2+s).re := by simp [s,line]; exact hσ.le
  have hχn := odd_character_ne_one χ (Finset.mem_filter.mp hχ).2
  have hKi : Integrable K := (smoothedPerronKernel_integral hX (by norm_num : (0:ℝ)<1)).1
  have hKv : (∫ τ : ℝ, K τ) = 1 := (smoothedPerronKernel_integral hX (by norm_num : (0:ℝ)<1)).2
  have hZi : Integrable (fun τ => K τ * Z τ) :=
    (perron_zeroDifference_integral hGRH χ hχn hX (by norm_num) hσ t).1
  have hZv : (∫ τ : ℝ, K τ * Z τ) = ∑' p : ZeroIndex χ.primitiveCharacter,
      smoothedPerronKernel X (p.val.1-(1/2+s)) :=
    (perron_zeroDifference_integral hGRH χ hχn hX (by norm_num) hσ t).2
  have hEi : Integrable (fun τ => E τ * K τ) :=
    (eulerCorrection_perron_integral χ hu hX (by norm_num : (0:ℝ)<1)).1
  have hEi0 := hKi.const_mul (eulerCorrection χ (1/2+s))
  have hgi0 := hKi.const_mul (-logDerivative χ s)
  have he (τ : ℝ) : -logDerivative χ (s+v τ) * K τ =
      (-logDerivative χ s)*K τ - K τ*Z τ + K τ*G τ - E τ*K τ +
        eulerCorrection χ (1/2+s)*K τ := by
    have hh := logDerivative_difference_zero_expansion hGRH χ hχ s (v τ)
      (by simpa [s,line] using hσ) (by simp [s,v,line]; linarith)
    dsimp [Z,G,E]
    linear_combination -K τ*hh
  have hp := smoothedPolynomial_perron_initial χ hX (by norm_num : (0:ℝ)<1)
    (1/2+s) (by simp [s,line]; linarith)
  have hp' : (∫ τ : ℝ, -logDerivative χ (s+v τ)*K τ) =
      smoothedDirichletPolynomial χ X (1/2+s) := by
    convert hp using 1
    congr 1
    funext τ
    congr 2
    dsimp [v]
    ring
  have hGi' : Integrable (fun τ => K τ * G τ) := hGi
  have h₁ : Integrable (fun τ => (-logDerivative χ s)*K τ-K τ*Z τ) := hgi0.sub hZi
  have h₂ : Integrable (fun τ => (-logDerivative χ s)*K τ-K τ*Z τ+K τ*G τ) := h₁.add hGi'
  have h₃ : Integrable (fun τ => (-logDerivative χ s)*K τ-K τ*Z τ+K τ*G τ-E τ*K τ) := h₂.sub hEi
  simp_rw [he] at hp'
  rw [integral_add h₃ hEi0, integral_sub h₂ hEi,
    integral_add h₁ hGi', integral_sub hgi0 hZi,
    integral_const_mul, integral_const_mul, hKv, mul_one, mul_one, hZv] at hp'
  have herror : -logDerivative χ s-smoothedDirichletPolynomial χ X (1/2+s) =
      ((∑' p : ZeroIndex χ.primitiveCharacter, smoothedPerronKernel X (p.val.1-(1/2+s))) -
        ∫ τ : ℝ, K τ*G τ) +
      ((∫ τ : ℝ, E τ*K τ)-eulerCorrection χ (1/2+s)) := by
    linear_combination hp'
  change ‖-logDerivative χ s-smoothedDirichletPolynomial χ X (1/2+s)‖ ≤ _
  rw [herror]
  apply (norm_add_le _ _).trans
  have hZb := (smoothedPerron_nontrivial_zero_sum_bound hGRH χ hχn hX hσ (t := t)).2
  have hEb := eulerCorrection_perron_error χ hu hX (by norm_num : (0:ℝ)<1)
  rw [norm_sub_rev] at hEb
  have hG : ‖∫ τ : ℝ, K τ*G τ‖ ≤ C := hGb
  have hz := norm_sub_le
    (∑' p : ZeroIndex χ.primitiveCharacter, smoothedPerronKernel X (p.val.1-(1/2+s)))
    (∫ τ : ℝ, K τ*G τ)
  dsimp [s] at hz ⊢
  dsimp [E,K,v,s] at hEb
  dsimp [E,K,v,s] at *
  linarith

end LiLiuGoldbach16
