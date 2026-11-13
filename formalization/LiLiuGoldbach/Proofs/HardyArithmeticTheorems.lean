import LiLiuGoldbach.Proofs.ArithmeticKernelRealization
import LiLiuGoldbach.Proofs.HardyKernelResidual
import LiLiuGoldbach.Proofs.CharacterGrowth
import LiLiuGoldbach.Proofs.ZetaTruncation

/-! Full arithmetic realization and point-evaluation conclusions from the proved growth estimates.
The generic kernel foundations are independent of the application theorems. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16

lemma arithmeticKernel_growth_inputs (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    ∃ L Z : ℝ, 0 ≤ L ∧ 0 ≤ Z ∧
      (∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc (alpha N) beta →
        ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2) ∧
      (∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * alpha N) →
        ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ)) := by
  obtain ⟨L, hL, hlog⟩ := logDerivative_uniform_bound (alpha N) beta (large_alpha_pos hlarge) ha.le
  obtain ⟨Z, hZ, hζ⟩ := riemannZeta_three_quarter_uniform
    (by linarith [large_alpha_pos hlarge] : 1 - 2 * alpha N < 1)
  refine ⟨L, Z, hL.le, hZ, ?_, hζ⟩
  intro χ hχ s hs
  have hh := hlog N inferInstance (large_parameters hlarge).1 hGRH χ
    (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2) s.re hs s.im
  have he : line s.re s.im = s := by apply Complex.ext <;> simp [line]
  simpa only [he] using hh

theorem proposition_5_3 (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    (∀ x ∈ ({alpha N, beta} : Finset ℝ), ∀ y ∈ ({alpha N, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
    IsHilbertSchmidt (residualOperator ha N) ∧ Nonempty (SpectralData (residualOperator ha N)) ∧
    (∑' j, eigenvalues (residualOperator ha N) j ^ 2) = hsNorm (residualOperator ha N) ^ 2 ∧
    hsNorm (residualOperator ha N) ^ 2 = BoundaryKernelSquareIntegral (alpha N) beta (weightedKernel N) ∧
    ‖residualOperator ha N‖ = sSup (Set.range (fun j => |eigenvalues (residualOperator ha N) j|)) ∧
    (residualOperator ha N ≠ 0 → ∃ j, |eigenvalues (residualOperator ha N) j| = ‖residualOperator ha N‖) := by
  obtain ⟨L, Z, hL, hZ, hlog, hζ⟩ := arithmeticKernel_growth_inputs N hlarge hGRH ha
  exact residualOperator_spec_of_growth N hlarge hGRH ha L Z hL hZ hlog hζ

theorem proposition_5_4_kernel_pairing (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (s z : ℂ) (hs : s ∈ strip (alpha N) beta) (hz : z ∈ strip (alpha N) beta) :
    weightedKernel N s z =
      paperInner (residualOperator ha N (evaluationVector z)) (evaluationVector s) := by
  obtain ⟨L, Z, hL, hZ, hlog, hζ⟩ := arithmeticKernel_growth_inputs N hlarge hGRH ha
  exact residualOperator_pairing_of_growth N hlarge hGRH ha L Z hL hZ hlog hζ s z hs hz

theorem proposition_5_3_kernel_integrability (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    ∀ (h : HardySpace (alpha N) beta) (s : ℂ), s ∈ strip (alpha N) beta →
      Integrable (fun t : ℝ => weightedKernel N s (line (alpha N) t) *
        (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => weightedKernel N s (line beta t) *
        (boundaryTraces ha h).2 t) := by
  obtain ⟨L, Z, hL, hZ, hlog, hζ⟩ := arithmeticKernel_growth_inputs N hlarge hGRH ha
  obtain ⟨_, hcol⟩ := weightedKernel_inputs_of_growth N hlarge hGRH ha L Z hL hZ hlog hζ
  exact kernelAction_integrable_of_hardyColumns ha (weightedKernel N) (weightedKernel_hermitian N) hcol

theorem proposition_5_4 (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (s z : ℂ) (hs : s ∈ strip (alpha N) beta) (hz : z ∈ strip (alpha N) beta) :
    (∀ h : HardySpace (alpha N) beta, fourierLaplace h s = paperInner h (evaluationVector s)) ∧
    fourierLaplace (evaluationVector z : HardySpace (alpha N) beta) s = reproducingKernel (alpha N) beta s z ∧
    ‖(evaluationVector s : HardySpace (alpha N) beta)‖ ^ 2 ≤ 1 / (8 * pointDistance (alpha N) beta s) ∧
    ‖residual N s (conj z)‖ ≤ ‖residualOperator ha N‖ * ‖1 + s‖ * ‖1 + z‖ /
      (8 * Real.sqrt (pointDistance (alpha N) beta s * pointDistance (alpha N) beta z)) := by
  exact ⟨evaluationVector_spec hs, evaluationVector_reproducingKernel ha hs hz,
    evaluationVector_norm_sq_le ha hs,
    residual_norm_le_of_kernel_pairing ha (large_alpha_pos hlarge).le N (residualOperator ha N)
      s z hs hz (proposition_5_4_kernel_pairing N hN hlarge hGRH ha s z hs hz)⟩

theorem proposition_5_4_fixed_contour : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_ : NeZero N), Even N → Real.exp 10 < (N : ℝ) → GRH N →
      ∀ ha : alpha N < beta, ∀ v t : ℝ,
        ‖residual N (line sigmaStar v) (line sigmaStar t)‖ ≤
          C * ‖residualOperator ha N‖ * (1 + |v| + |t|) ^ 2 := by
  refine ⟨45, by norm_num, ?_⟩
  intro N hNZ hN hlarge hGRH ha v t
  exact residual_fixed_contour_bound_of_pairing N hlarge ha (residualOperator ha N)
    (proposition_5_4_kernel_pairing N hN hlarge hGRH ha) v t

end LiLiuGoldbach16
