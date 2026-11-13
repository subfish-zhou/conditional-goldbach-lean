import LiLiuGoldbach.Proofs.QuadraticNormChange
import LiLiuGoldbach.Proofs.Asymptotics

/-! Strict energy positivity and uniform norm bounds for arbitrary strip widths. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

lemma derivativeWeight_nonzero_of_weight {φ : ℝ → ℝ} (hφ : IsWeight φ) :
    ∃ u : ℝ, 0 < u ∧ derivativeWeight φ u ≠ 0 := by
  have hne : ∃ u, φ u ≠ 0 := by
    by_contra he
    push Not at he
    exact hφ.2.2.2.2 (funext he)
  obtain ⟨u,hu⟩ := hne
  have hus := hφ.mem_support_interval hu
  have hu0 : 0 < u := by linarith [hus.1]
  have hψu : 0 < companion φ u := mul_pos (Real.sqrt_pos.mpr hu0)
    (lt_of_le_of_ne (hφ.nonneg u) hu.symm)
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1/3 : ℝ) (2/3)).Nonempty from ⟨u,hus⟩)
    (companion_contDiff hφ).continuous.continuousOn
  have hψv : 0 < companion φ v := hψu.trans_le (hmax hus)
  have hv0 : 0 < v := by linarith [hv.1]
  have hglobal (x : ℝ) : companion φ x ≤ companion φ v := by
    by_cases hx : x ∈ Icc (1/3 : ℝ) (2/3)
    · exact hmax hx
    · have hz : companion φ x = 0 := by
        by_contra he
        exact hx (companion_support_subset hφ he)
      rw [hz]
      exact hψv.le
  have hl : IsLocalMax (companion φ) v := Filter.Eventually.of_forall hglobal
  refine ⟨v,hv0,?_⟩
  simpa [derivativeWeight, hl.deriv_eq_zero] using hψv.ne'

lemma weightEnergy_pos {φ : ℝ → ℝ} (hφ : IsWeight φ) : 0 < weightEnergy φ := by
  obtain ⟨u,hu,hd⟩ := derivativeWeight_nonzero_of_weight hφ
  let f : ℝ → ℝ := fun x => derivativeWeight φ x^2/x
  have hs : Function.support f ⊆ Icc (1/3 : ℝ) (2/3) := by
    intro x hx
    apply derivativeWeight_support_subset hφ
    intro he
    exact hx (by simp [f,he])
  have hc : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (show (0 : ℝ)<1/3 by norm_num)] with x hx
      have hz : f x = 0 := by
        by_contra he
        exact (not_lt_of_ge (hs he).1) hx
      exact hz
    · exact ((derivativeWeight_continuous hφ).continuousAt.pow 2).div continuousAt_id hx
  have hf : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  have hn : 0 ≤ f := by
    intro x
    change 0 ≤ f x
    by_cases hx : f x = 0
    · rw [hx]
    · exact div_nonneg (sq_nonneg _) (by have hh := (hs hx).1; linarith)
  have hp : 0 < ∫ x, f x := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hf hn
    (show f u ≠ 0 from div_ne_zero (pow_ne_zero _ hd) hu.ne')
  have he : (∫ x, f x) = ∫ x in Ioi (0 : ℝ), f x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra he
    have hh := (hs he).1
    exact hx (show 0<x by linarith)
  rw [he] at hp
  exact mul_pos (by positivity : 0 < (2*Real.pi)⁻¹) hp

lemma normFunctional_uniform_upper (N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (a : ℝ) (ha : 0 ≤ a) :
    normFunctional N φ a ≤ (N : ℝ)^(2*a)*weightEnergy φ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hE,hQ⟩ := proposition_7_4_norm_integrals N hN φ hφ a
  simp only [Real.rpow_eq_pow] at hQ
  have hb : (∫ u in Ioi (0 : ℝ), (N*u)^(2*a)*derivativeWeight φ u^2 /
      (1+(N*u)^(-2*(beta-a)))/u) ≤
      ∫ u in Ioi (0 : ℝ), (N : ℝ)^(2*a)*(derivativeWeight φ u^2/u) := by
    apply setIntegral_mono_on hQ (hE.const_mul _) measurableSet_Ioi
    intro u hu
    change 0 < u at hu
    by_cases hd : derivativeWeight φ u = 0
    · simp [hd]
    · have hs := derivativeWeight_support_subset hφ hd
      have hNu0 : 0 ≤ (N : ℝ)*u := by positivity
      have hNu : (N : ℝ)*u ≤ N := by nlinarith [hs.2]
      have hp := Real.rpow_le_rpow hNu0 hNu (show 0 ≤ 2*a by positivity)
      have hv : 0 ≤ (N*u)^(-2*(beta-a)) := by positivity
      calc
        _ ≤ ((N*u)^(2*a)*derivativeWeight φ u^2)/u :=
          div_le_div_of_nonneg_right (div_le_self (by positivity) (by linarith)) hu.le
        _ ≤ ((N : ℝ)^(2*a)*derivativeWeight φ u^2)/u :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) hu.le
        _ = _ := by ring
  rw [integral_const_mul] at hb
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2*Real.pi)⁻¹ by positivity)
  unfold normFunctional weightEnergy
  simp only [Real.rpow_eq_pow]
  convert hh using 1 <;> ring

lemma normFunctional_uniform_lower (N : ℕ) (hN : 3 ≤ N) (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (a : ℝ) (ha : 0 < a) (ha' : a < 1/10) :
    (N : ℝ)^(2*a)*(weightEnergy φ/6) ≤ normFunctional N φ a := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < N := by omega
  have hNr0 : (0 : ℝ) < N := by linarith
  obtain ⟨hE,hQ⟩ := proposition_7_4_norm_integrals N hN0 φ hφ a
  simp only [Real.rpow_eq_pow] at hQ
  have hb : (∫ u in Ioi (0 : ℝ), ((N : ℝ)^(2*a)/6)*(derivativeWeight φ u^2/u)) ≤
      ∫ u in Ioi (0 : ℝ), (N*u)^(2*a)*derivativeWeight φ u^2 /
        (1+(N*u)^(-2*(beta-a)))/u := by
    apply setIntegral_mono_on (hE.const_mul _) hQ measurableSet_Ioi
    intro u hu
    change 0 < u at hu
    by_cases hd : derivativeWeight φ u = 0
    · simp [hd]
    · have hs := derivativeWeight_support_subset hφ hd
      have hu1 : u ≤ 1 := by linarith [hs.2]
      have hNu : 1 ≤ (N : ℝ)*u := by nlinarith [hs.1]
      have huPow : 1/3 ≤ u^(2*a) := by
        have hh := Real.rpow_le_rpow_of_exponent_ge hu hu1 (show 2*a ≤ 1 by linarith)
        rw [Real.rpow_one] at hh
        exact hs.1.trans hh
      have hNum : (N : ℝ)^(2*a)/3 ≤ (N*u)^(2*a) := by
        rw [Real.mul_rpow hNr0.le hu.le]
        have hh := mul_le_mul_of_nonneg_left huPow (Real.rpow_nonneg hNr0.le (2*a))
        nlinarith
      have hv0 : 0 ≤ (N*u)^(-2*(beta-a)) := by positivity
      have hv : (N*u)^(-2*(beta-a)) ≤ 1 := by
        have hh := Real.rpow_le_rpow_of_exponent_le hNu
          (show -2*(beta-a) ≤ 0 by dsimp [beta]; linarith)
        simpa using hh
      have hfrac : (N : ℝ)^(2*a)/6 ≤ (N*u)^(2*a)/(1+(N*u)^(-2*(beta-a))) := by
        apply (le_div_iff₀ (by positivity)).2
        have hp := Real.rpow_nonneg hNr0.le (2*a)
        nlinarith
      have hh := mul_le_mul_of_nonneg_right hfrac
        (div_nonneg (sq_nonneg (derivativeWeight φ u)) hu.le)
      convert hh using 1 <;> ring
  rw [integral_const_mul] at hb
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2*Real.pi)⁻¹ by positivity)
  unfold normFunctional weightEnergy
  simp only [Real.rpow_eq_pow]
  convert hh using 1 <;> ring

lemma nat_rpow_alpha (N : ℕ) (hN : 1 < N) (c : ℝ) :
    (N : ℝ)^(2*alpha N c) = Real.exp (2*c) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hl : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [Real.rpow_def_of_pos hNr]
  congr 1
  unfold alpha
  field_simp

end LiLiuGoldbach16
