import ConditionalGoldbach.Proofs.Elementary
import ConditionalGoldbach.Proofs.WeightNorm
import ConditionalGoldbach.Proofs.SpectralAlgebra
import ConditionalGoldbach.Proofs.DictionaryApplication

/-! Assembly of the audited main statements from the proved Hardy operator realization,
exact quadratic identity, and spectral dictionary. The paper's GRH and spectral
hypotheses remain explicit in the conclusions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

theorem theorem_7_1_uniform (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (ha : alpha N < beta) :
    |weightMass φ * singularSeries N - goldbach N φ| ≤
      Real.exp 2 * weightEnergy φ * ‖residualOperator ha N‖ := by
  exact (theorem_7_1 N hN hlarge hGRH φ hφ ha).2.trans
    (mul_le_mul_of_nonneg_right (normFunctional_le_exp2_weightEnergy N hlarge φ hφ)
      (norm_nonneg _))

/-- Turning the uniform relative error into an asymptotic needs positive mass,
positive singular series, and the prescribed growth of h. -/
theorem evenAsymptotic_of_error_bound (f S h : ℕ → ℝ) (m C : ℝ)
    (hm : 0 < m) (hC : 0 < C) (hS : ∀ N, 0 < S N)
    (hinfty : EvenTendstoInfinity h)
    (hbound : EvenEventually (fun N => |f N - m * S N| ≤ C * S N / h N)) :
    EvenAsymptotic f (fun N => m * S N) := by
  intro ε hε
  obtain ⟨n, hn⟩ := hbound
  obtain ⟨k, hk⟩ := hinfty (C / (m * ε) + 1)
  refine ⟨max n k, fun N hN he => ?_⟩
  have hb := hn N (le_trans (le_max_left _ _) hN) he
  have hh := hk N (le_trans (le_max_right _ _) hN) he
  have hmε : 0 < m * ε := mul_pos hm hε
  have hhpos : 0 < h N := by
    have := div_pos hC hmε
    linarith
  have hsmall : C / (m * h N) < ε := by
    apply (div_lt_iff₀ (mul_pos hm hhpos)).2
    have hdiv : C / (m * ε) < h N := by linarith
    have := (div_lt_iff₀ hmε).1 hdiv
    nlinarith
  have hden : 0 < m * S N := mul_pos hm (hS N)
  change |f N / (m * S N) - 1| < ε
  rw [div_sub_one (ne_of_gt hden), abs_div, abs_of_pos hden]
  calc
    |f N - m * S N| / (m * S N) ≤ (C * S N / h N) / (m * S N) :=
      div_le_div_of_nonneg_right hb hden.le
    _ = C / (m * h N) := by field_simp [ne_of_gt (hS N), ne_of_gt hm, ne_of_gt hhpos]
    _ < ε := hsmall

theorem theorem_1_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ → ℝ,
      EvenEventually GRH → HypothesisS h →
      EvenEventually (fun N => |goldbach N φ - weightMass φ * singularSeries N| ≤
        C * singularSeries N / h N) ∧
      EvenAsymptotic (fun N => goldbach N φ) (fun N => weightMass φ * singularSeries N) := by
  let A : ℝ := Real.exp 2 * weightEnergy φ
  have hA : 0 ≤ A := mul_nonneg (Real.exp_pos 2).le (weightEnergy_nonneg φ)
  let C : ℝ := A + 1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, fun h hGRH hS => ?_⟩
  have hbound : EvenEventually (fun N =>
      |goldbach N φ - weightMass φ * singularSeries N| ≤ C * singularSeries N / h N) := by
    obtain ⟨k, hk⟩ := hGRH.and (hS.2.and (hS.1.2.2.and evenEventually_large))
    refine ⟨k, fun N hNk he => ?_⟩
    rcases hk N hNk he with ⟨hG, hSpectral, hwidth, hlarge⟩
    rcases large_parameters hlarge with ⟨hN4, hlog, ha⟩
    have hNpos : 0 < N := by omega
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
    let : NeZero N := ⟨ne_of_gt hNpos⟩
    have hh : 0 < h N := hS.1.1 N he hN4
    have hsing := singularSeries_pos N
    have hη : 0 < zeroFreeWidth N h := by unfold zeroFreeWidth; positivity
    have hηhalf : zeroFreeWidth N h < 1 / 2 := by linarith
    have hnorm := ((theorem_6_1 N he hlarge hG ha).2.1
      (zeroFreeWidth N h) hη hηhalf).1 (hSpectral hG inferInstance ha)
    have hnorm' : ‖residualOperator ha N‖ ≤ singularSeries N / h N :=
      hnorm.trans (spectralScale_div_sqrt_width_le N h hNR hsing hlog hh hwidth)
    have herr : |goldbach N φ - weightMass φ * singularSeries N| ≤
        A * ‖residualOperator ha N‖ := by
      simpa only [A, abs_sub_comm] using theorem_7_1_uniform N he hlarge hG φ hφ ha
    calc
      _ ≤ A * ‖residualOperator ha N‖ := herr
      _ ≤ A * (singularSeries N / h N) := mul_le_mul_of_nonneg_left hnorm' hA
      _ ≤ C * singularSeries N / h N := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        exact (div_pos hsing hh).le
  exact ⟨hbound, evenAsymptotic_of_error_bound (fun N => goldbach N φ)
    singularSeries h (weightMass φ) C (weightMass_pos hφ) hC singularSeries_pos
      hS.1.2.1 hbound⟩

theorem theorem_1_2 (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (hGRH : EvenEventually GRH) (hR : HypothesisR) :
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N) := by
  let A : ℝ := Real.exp 2 * weightEnergy φ
  have hA : 0 ≤ A := mul_nonneg (Real.exp_pos 2).le (weightEnergy_nonneg φ)
  refine ⟨A + 1, by linarith, ?_⟩
  obtain ⟨k, hk⟩ := hGRH.and (hR.and evenEventually_large)
  refine ⟨k, fun N hNk he => ?_⟩
  rcases hk N hNk he with ⟨hG, hSpectral, hlarge⟩
  rcases large_parameters hlarge with ⟨hN4, hlog, ha⟩
  have hNpos : 0 < N := by omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  let : NeZero N := ⟨ne_of_gt hNpos⟩
  have hnorm := (theorem_6_1 N he hlarge hG ha).1.1
    (hSpectral hG inferInstance ha)
  have herr : |goldbach N φ - weightMass φ * singularSeries N| ≤
      A * ‖residualOperator ha N‖ := by
    simpa only [A, abs_sub_comm] using theorem_7_1_uniform N he hlarge hG φ hφ ha
  calc
    _ ≤ A * ‖residualOperator ha N‖ := herr
    _ ≤ A * spectralScale N := mul_le_mul_of_nonneg_left hnorm hA
    _ ≤ (A + 1) * spectralScale N :=
      mul_le_mul_of_nonneg_right (by linarith)
        (spectralScale_pos N hNR (singularSeries_pos N) hlog).le

end ConditionalGoldbach
