module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import ConditionalGoldbach.Proofs.QuadraticDensity

/-! Explicit Riesz vectors for compactly supported density functionals. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma weighted_test_memLp (a b : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g) :
    MemLp (fun τ : ℝ => ((g τ / hardyWeight a b τ : ℝ) : ℂ)) 2 (hardyMeasure a b) := by
  let f : ℝ → ℂ := fun τ => ((g τ / hardyWeight a b τ : ℝ) : ℂ)
  have hc : Continuous f := Complex.continuous_ofReal.comp
    (hg.div (hardyWeight_continuous a b) (fun τ => (hardyWeight_pos a b τ).ne'))
  have hcont : Continuous (fun τ => ‖f τ‖ ^ 2 * hardyWeight a b τ) :=
    (hc.norm.pow 2).mul (hardyWeight_continuous a b)
  have hs : HasCompactSupport (fun τ => ‖f τ‖ ^ 2 * hardyWeight a b τ) := by
    apply HasCompactSupport.of_support_subset_isCompact hgs.isCompact
    intro τ hτ
    apply subset_tsupport
    intro hgzero
    exact hτ (by simp [f, hgzero])
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  change Integrable (fun τ => ‖f τ‖ ^ 2)
    (volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ)))
  rw [integrable_withDensity_iff (hardyWeight_continuous a b).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (hardyWeight_pos a b _).le, smul_eq_mul, mul_comm] using
    hcont.integrable_of_hasCompactSupport hs

def weightedTestVector (a b : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g) :
    HardySpace a b := (weighted_test_memLp a b g hg hgs).toLp _

lemma weightedTestVector_pairing (a b : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (hgs : HasCompactSupport g) (ψ : HardySpace a b) :
    paperInner ψ (weightedTestVector a b g hg hgs) = ∫ τ : ℝ, ψ τ * (g τ : ℂ) := by
  have hcoe := (weighted_test_memLp a b g hg hgs).coeFn_toLp
  unfold paperInner
  rw [L2.inner_def]
  calc
    (∫ τ : ℝ, inner ℂ ((weightedTestVector a b g hg hgs) τ) (ψ τ) ∂hardyMeasure a b)
        = ∫ τ : ℝ, ψ τ * ((g τ / hardyWeight a b τ : ℝ) : ℂ) ∂hardyMeasure a b := by
      apply integral_congr_ae
      filter_upwards [hcoe] with τ hτ
      simp only [weightedTestVector, hτ, RCLike.inner_apply, Complex.conj_ofReal]
    _ = _ := by
      change (∫ τ : ℝ, ψ τ * ((g τ / hardyWeight a b τ : ℝ) : ℂ)
        ∂(volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ)))) = _
      rw [integral_withDensity_eq_integral_toReal_smul
        (hardyWeight_continuous a b).measurable.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with τ
      simp only [ENNReal.toReal_ofReal (hardyWeight_pos a b τ).le, Complex.real_smul,
        Complex.ofReal_div]
      have hw : (hardyWeight a b τ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (hardyWeight_pos a b τ).ne'
      field_simp

lemma weightedTestVector_norm_sq (a b : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    ‖weightedTestVector a b g hg hgs‖ ^ 2 = ∫ τ : ℝ, g τ ^ 2 / hardyWeight a b τ := by
  rw [hardySpace_norm_sq_integral]
  have hcoe := ((weighted_test_memLp a b g hg hgs).coeFn_toLp).filter_mono
    (volume_absolutelyContinuous_hardyMeasure a b).ae_le
  apply integral_congr_ae
  filter_upwards [hcoe] with τ hτ
  simp only [weightedTestVector, hτ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hw := (hardyWeight_pos a b τ).ne'
  field_simp

lemma derivativeDensity_continuous (N : ℕ) (_hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    Continuous (fun τ : ℝ => derivativeWeight φ (Real.exp (-τ) / N)) := by
  apply (derivativeWeight_continuous hφ).comp
  fun_prop

lemma derivativeDensity_hasCompactSupport (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    HasCompactSupport (fun τ : ℝ => derivativeWeight φ (Real.exp (-τ) / N)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -Real.log ((2 / 3) * N)) (b := -Real.log ((1 / 3) * N)))
  intro τ hτ
  have hs := derivativeWeight_support_subset hφ hτ
  have hlo := (le_div_iff₀ hNr).1 hs.1
  have hhi := (div_le_iff₀ hNr).1 hs.2
  have hl := Real.log_le_log (show 0 < (1 / 3 : ℝ) * N by positivity) hlo
  have hr := Real.log_le_log (Real.exp_pos (-τ)) hhi
  rw [Real.log_exp] at hl hr
  constructor <;> linarith


theorem functional_riesz_exists {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ v : HardySpace a beta,
      (∀ σ ∈ Ioo a beta, ∀ ψ : HardySpace a beta,
        functionalValue N φ σ ψ = paperInner ψ v) ∧
      ‖v‖ ^ 2 = (2 * Real.pi)⁻¹ * ∫ τ : ℝ,
        derivativeWeight φ (Real.exp (-τ) / N) ^ 2 / hardyWeight a beta τ := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  let g : ℝ → ℝ := fun τ => c * derivativeWeight φ (Real.exp (-τ) / N)
  have hg : Continuous g := (derivativeDensity_continuous N hN φ hφ).const_mul c
  have hgs : HasCompactSupport g := (derivativeDensity_hasCompactSupport N hN φ hφ).mul_left
  refine ⟨weightedTestVector a beta g hg hgs, ?_, ?_⟩
  · intro σ hσ ψ
    rw [weightedTestVector_pairing, functionalValue_density N hN φ hφ σ hσ]
    dsimp [g, c]
    push_cast
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with τ
    ring
  · rw [weightedTestVector_norm_sq]
    dsimp [g]
    simp only [mul_pow, mul_div_assoc, integral_const_mul]
    congr 1
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (by positivity)]


theorem rieszVector_density_spec {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (ha : sigmaStar ∈ Ioo a beta) :
    (∀ σ ∈ Ioo a beta, ∀ ψ : HardySpace a beta,
      functionalValue N φ σ ψ = paperInner ψ (rieszVector N φ)) ∧
    ‖(rieszVector N φ : HardySpace a beta)‖ ^ 2 = (2 * Real.pi)⁻¹ * ∫ τ : ℝ,
      derivativeWeight φ (Real.exp (-τ) / N) ^ 2 / hardyWeight a beta τ := by
  obtain ⟨v, hv, hn⟩ := functional_riesz_exists (a := a) N hN φ hφ
  have hex : ∃ v : HardySpace a beta, ∀ ψ,
      functionalValue N φ sigmaStar ψ = paperInner ψ v := ⟨v, hv sigmaStar ha⟩
  have hspec : ∀ ψ : HardySpace a beta,
      functionalValue N φ sigmaStar ψ = paperInner ψ (rieszVector N φ) := by
    unfold rieszVector
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  have heq : (rieszVector N φ : HardySpace a beta) = v := by
    apply ext_inner_right ℂ
    intro ψ
    change paperInner ψ (rieszVector N φ) = paperInner ψ v
    exact (hspec ψ).symm.trans (hv sigmaStar ha ψ)
  rw [heq]
  exact ⟨hv, hn⟩

theorem functionalValue_continuousLinearMap {a : ℝ} (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (σ : ℝ) (hσ : σ ∈ Ioo a beta) :
    ∃ ℓ : HardySpace a beta →L[ℂ] ℂ,
      (∀ ψ, ℓ ψ = functionalValue N φ σ ψ) ∧
      ‖ℓ‖ ^ 2 = (2 * Real.pi)⁻¹ * ∫ τ : ℝ,
        derivativeWeight φ (Real.exp (-τ) / N) ^ 2 / hardyWeight a beta τ := by
  obtain ⟨v, hv, hn⟩ := functional_riesz_exists (a := a) N hN φ hφ
  refine ⟨InnerProductSpace.toDual ℂ (HardySpace a beta) v, ?_, ?_⟩
  · intro ψ
    exact (hv σ hσ ψ).symm
  · rw [LinearIsometryEquiv.norm_map]
    exact hn

end ConditionalGoldbach
