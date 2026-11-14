module

public import ConditionalGoldbach.Proofs.KernelGrowthBounds
public import ConditionalGoldbach.Proofs.KernelRegularity
public import ConditionalGoldbach.Proofs.HardyKernelMajorant

/-! The arithmetic Hardy realization from its two explicit vertical growth estimates. -/
public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma weightedKernel_closed_joint_continuous (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) :
    ContinuousOn (Function.uncurry (weightedKernel N))
      {p : ℂ × ℂ | p.1.re ∈ Icc (alpha N) beta ∧ p.2.re ∈ Icc (alpha N) beta} := by
  have hN : 0 < N := by have := (large_parameters hlarge).1; omega
  have hc := (weightedKernel_conj_differentiableOn N hN hGRH).continuousOn
  have hj : ContinuousOn (fun p : ℂ × ℂ => weightedKernel N p.1 (conj (conj p.2)))
      {p : ℂ × ℂ | p.1.re ∈ Icc (alpha N) beta ∧ p.2.re ∈ Icc (alpha N) beta} := by
    apply hc.comp (f := fun p : ℂ × ℂ => (p.1, conj p.2)) (by fun_prop)
    intro p hp
    exact large_closed_strip_subset hlarge ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  change ContinuousOn (fun p : ℂ × ℂ => weightedKernel N p.1 p.2) _
  simpa only [Complex.conj_conj] using hj

lemma weightedKernel_inputs_of_growth (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc (alpha N) beta →
      ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2)
    (hζ : ∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * alpha N) →
      ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ)) :
    (∀ x ∈ ({alpha N, beta} : Finset ℝ), ∀ y ∈ ({alpha N, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
      HasHardyKernelColumns ha (weightedKernel N) := by
  have hN4 := (large_parameters hlarge).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog' : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc (alpha N) beta →
      ‖logDerivative χ s‖ ≤ (L * (64 * (2 * N) ^ (1 / 4 : ℝ))) *
        (1 + |s.im|) ^ (1 / 4 : ℝ) := by
    intro χ hχ s hs
    calc
      _ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2 := hlog χ hχ s hs
      _ ≤ L * ((64 * (2 * N) ^ (1 / 4 : ℝ)) * (1 + |s.im|) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hN1 s.im) hL
      _ = _ := by ring
  obtain ⟨P, hP, hchar⟩ := characterKernel_power_bound N _ (by positivity) hlog'
  obtain ⟨Q, hQ, hmodel⟩ := continuedModel_power_bound (large_alpha_pos hlarge) ha N hN4 Z hZ hζ
  obtain ⟨C, hC, hR⟩ := residual_power_bound_of_components (large_alpha_pos hlarge) N P Q hP hQ hchar hmodel
  apply hardyKernel_inputs_of_power_bound ha (weightedKernel N)
    (weightedKernel_closed_joint_continuous N hlarge hGRH)
    (fun z hz => (weightedKernel_closed_column_regular N hlarge hGRH z hz).1)
    (16 * C ^ 2) (by positivity)
  exact weightedKernel_power_bound_of_residual (large_alpha_pos hlarge).le N C hC hR

lemma residualOperator_spec_of_growth (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc (alpha N) beta →
      ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2)
    (hζ : ∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * alpha N) →
      ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ)) :
    (∀ x ∈ ({alpha N, beta} : Finset ℝ), ∀ y ∈ ({alpha N, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
    IsHilbertSchmidt (residualOperator ha N) ∧ Nonempty (SpectralData (residualOperator ha N)) ∧
    (∑' j, eigenvalues (residualOperator ha N) j ^ 2) = hsNorm (residualOperator ha N) ^ 2 ∧
    hsNorm (residualOperator ha N) ^ 2 = BoundaryKernelSquareIntegral (alpha N) beta (weightedKernel N) ∧
    ‖residualOperator ha N‖ = sSup (Set.range (fun j => |eigenvalues (residualOperator ha N) j|)) ∧
    (residualOperator ha N ≠ 0 → ∃ j, |eigenvalues (residualOperator ha N) j| = ‖residualOperator ha N‖) := by
  obtain ⟨hK, hcol⟩ := weightedKernel_inputs_of_growth N hlarge hGRH ha L Z hL hZ hlog hζ
  exact ⟨hK, kernelOperator_spec_of_hardyColumns ha N (weightedKernel N) (weightedKernel_hermitian N) hK hcol⟩

lemma residualOperator_pairing_of_growth (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc (alpha N) beta →
      ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2)
    (hζ : ∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * alpha N) →
      ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ))
    (s z : ℂ) (hs : s ∈ strip (alpha N) beta) (hz : z ∈ strip (alpha N) beta) :
    weightedKernel N s z = paperInner (residualOperator ha N (evaluationVector z)) (evaluationVector s) := by
  obtain ⟨hK, hcol⟩ := weightedKernel_inputs_of_growth N hlarge hGRH ha L Z hL hZ hlog hζ
  exact kernelOperator_pairing_of_hardyColumns ha N (weightedKernel N) (weightedKernel_hermitian N) hK hcol s z hs hz

end ConditionalGoldbach
