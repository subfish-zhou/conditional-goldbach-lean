import ConditionalGoldbach.Proofs.HardyKernelResidual
import ConditionalGoldbach.Proofs.CharacterGrowth
import ConditionalGoldbach.Proofs.ZetaTruncation
import ConditionalGoldbach.Proofs.KernelGrowthBounds
import ConditionalGoldbach.Proofs.KernelRegularity
import ConditionalGoldbach.Proofs.HardyKernelMajorant

/-! The arithmetic Hardy realization from its two explicit vertical growth estimates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma closed_strip_subset_at {a : ℝ} (ha0 : 0 < a) :
    {p : ℂ × ℂ | a ≤ p.1.re ∧ p.1.re ≤ beta ∧ a ≤ p.2.re ∧ p.2.re ≤ beta} ⊆ analyticDomain := by
  intro p hp
  exact ⟨ha0.trans_le hp.1, hp.2.1.trans_lt (by norm_num [beta]),
    ha0.trans_le hp.2.2.1, hp.2.2.2.trans_lt (by norm_num [beta])⟩

lemma weightedKernel_closed_column_regular_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (z : ℂ)
    (hz : a ≤ z.re ∧ z.re ≤ beta) :
    DifferentiableOn ℂ (fun s => weightedKernel N s z) (strip a beta) ∧
    ContinuousOn (fun s => weightedKernel N s z) {s | a ≤ s.re ∧ s.re ≤ beta} := by
  have hd (s : ℂ) (hs : a ≤ s.re ∧ s.re ≤ beta) :
      DifferentiableAt ℂ (fun w => weightedKernel N w z) s :=
    weightedKernel_column_differentiableAt N (by omega) hGRH s z
      (closed_strip_subset_at ha0 ⟨hs.1, hs.2, hz.1, hz.2⟩)
  exact ⟨fun s hs => (hd s ⟨hs.1.le, hs.2.le⟩).differentiableWithinAt,
    fun s hs => (hd s hs).continuousAt.continuousWithinAt⟩


lemma weightedKernel_closed_joint_continuous_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) :
    ContinuousOn (Function.uncurry (weightedKernel N))
      {p : ℂ × ℂ | p.1.re ∈ Icc a beta ∧ p.2.re ∈ Icc a beta} := by
  have hN : 0 < N := by have := hN4; omega
  have hc := (weightedKernel_conj_differentiableOn N hN hGRH).continuousOn
  have hj : ContinuousOn (fun p : ℂ × ℂ => weightedKernel N p.1 (conj (conj p.2)))
      {p : ℂ × ℂ | p.1.re ∈ Icc a beta ∧ p.2.re ∈ Icc a beta} := by
    apply hc.comp (f := fun p : ℂ × ℂ => (p.1, conj p.2)) (by fun_prop)
    intro p hp
    exact closed_strip_subset_at ha0 ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  change ContinuousOn (fun p : ℂ × ℂ => weightedKernel N p.1 p.2) _
  simpa only [Complex.conj_conj] using hj

lemma weightedKernel_inputs_of_growth_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc a beta →
      ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2)
    (hζ : ∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * a) →
      ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ)) :
    (∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
      HasHardyKernelColumns ha (weightedKernel N) := by
  have hN4 := hN4
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog' : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc a beta →
      ‖logDerivative χ s‖ ≤ (L * (64 * (2 * N) ^ (1 / 4 : ℝ))) *
        (1 + |s.im|) ^ (1 / 4 : ℝ) := by
    intro χ hχ s hs
    calc
      _ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2 := hlog χ hχ s hs
      _ ≤ L * ((64 * (2 * N) ^ (1 / 4 : ℝ)) * (1 + |s.im|) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hN1 s.im) hL
      _ = _ := by ring
  obtain ⟨P, hP, hchar⟩ := characterKernel_power_bound N _ (by positivity) hlog'
  obtain ⟨Q, hQ, hmodel⟩ := continuedModel_power_bound ha0 ha N hN4 Z hZ hζ
  obtain ⟨C, hC, hR⟩ := residual_power_bound_of_components ha0 N P Q hP hQ hchar hmodel
  apply hardyKernel_inputs_of_power_bound ha (weightedKernel N)
    (weightedKernel_closed_joint_continuous_at a N ha0 hN4 hGRH)
    (fun z hz => (weightedKernel_closed_column_regular_at a N ha0 hN4 hGRH z hz).1)
    (16 * C ^ 2) (by positivity)
  exact weightedKernel_power_bound_of_residual ha0.le N C hC hR

lemma residualOperator_spec_of_growth_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc a beta →
      ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2)
    (hζ : ∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * a) →
      ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ)) :
    (∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
    IsHilbertSchmidt (residualOperator ha N) ∧ Nonempty (SpectralData (residualOperator ha N)) ∧
    (∑' j, eigenvalues (residualOperator ha N) j ^ 2) = hsNorm (residualOperator ha N) ^ 2 ∧
    hsNorm (residualOperator ha N) ^ 2 = BoundaryKernelSquareIntegral a beta (weightedKernel N) ∧
    ‖residualOperator ha N‖ = sSup (Set.range (fun j => |eigenvalues (residualOperator ha N) j|)) ∧
    (residualOperator ha N ≠ 0 → ∃ j, |eigenvalues (residualOperator ha N) j| = ‖residualOperator ha N‖) := by
  obtain ⟨hK, hcol⟩ := weightedKernel_inputs_of_growth_at a N ha0 hN4 hGRH ha L Z hL hZ hlog hζ
  exact ⟨hK, kernelOperator_spec_of_hardyColumns ha N (weightedKernel N) (weightedKernel_hermitian N) hK hcol⟩

lemma residualOperator_pairing_of_growth_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc a beta →
      ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2)
    (hζ : ∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * a) →
      ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ))
    (s z : ℂ) (hs : s ∈ strip a beta) (hz : z ∈ strip a beta) :
    weightedKernel N s z = paperInner (residualOperator ha N (evaluationVector z)) (evaluationVector s) := by
  obtain ⟨hK, hcol⟩ := weightedKernel_inputs_of_growth_at a N ha0 hN4 hGRH ha L Z hL hZ hlog hζ
  exact kernelOperator_pairing_of_hardyColumns ha N (weightedKernel N) (weightedKernel_hermitian N) hK hcol s z hs hz

lemma arithmeticKernel_growth_inputs_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta) :
    ∃ L Z : ℝ, 0 ≤ L ∧ 0 ≤ Z ∧
      (∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc a beta →
        ‖logDerivative χ s‖ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2) ∧
      (∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * a) →
        ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ)) := by
  obtain ⟨L, hL, hlog⟩ := logDerivative_uniform_bound a beta ha0 ha.le
  obtain ⟨Z, hZ, hζ⟩ := riemannZeta_three_quarter_uniform
    (by linarith : 1 - 2 * a < 1)
  refine ⟨L, Z, hL.le, hZ, ?_, hζ⟩
  intro χ hχ s hs
  have hh := hlog N inferInstance hN4 hGRH χ
    (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2) s.re hs s.im
  have he : line s.re s.im = s := by apply Complex.ext <;> simp [line]
  simpa only [he] using hh

lemma residualOperator_pairing_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta)
    (s z : ℂ) (hs : s ∈ strip a beta) (hz : z ∈ strip a beta) :
    weightedKernel N s z = paperInner (residualOperator ha N (evaluationVector z)) (evaluationVector s) := by
  obtain ⟨L,Z,hL,hZ,hlog,hζ⟩ := arithmeticKernel_growth_inputs_at a N ha0 hN4 hGRH ha
  exact residualOperator_pairing_of_growth_at a N ha0 hN4 hGRH ha L Z hL hZ hlog hζ s z hs hz

lemma alpha_pos_at (N : ℕ) (hN4 : 4 ≤ N) (c : ℝ) (hc : 0 < c) : 0 < alpha N c := by
  exact div_pos hc (Real.log_pos (by exact_mod_cast (show 1<N by omega)))

lemma residualOperator_spec_at (a : ℝ) (N : ℕ) [NeZero N] (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta) :
    (∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
    IsHilbertSchmidt (residualOperator ha N) ∧ Nonempty (SpectralData (residualOperator ha N)) ∧
    (∑' j, eigenvalues (residualOperator ha N) j ^ 2) = hsNorm (residualOperator ha N) ^ 2 ∧
    hsNorm (residualOperator ha N) ^ 2 = BoundaryKernelSquareIntegral a beta (weightedKernel N) ∧
    ‖residualOperator ha N‖ = sSup (Set.range (fun j => |eigenvalues (residualOperator ha N) j|)) ∧
    (residualOperator ha N ≠ 0 → ∃ j, |eigenvalues (residualOperator ha N) j| = ‖residualOperator ha N‖) := by
  obtain ⟨L, Z, hL, hZ, hlog, hζ⟩ := arithmeticKernel_growth_inputs_at a N ha0 hN4 hGRH ha
  exact residualOperator_spec_of_growth_at a N ha0 hN4 hGRH ha L Z hL hZ hlog hζ

theorem proposition_A_1_operator_spec (N : ℕ) [NeZero N] (hN : Even N)
    (hN4 : 4 ≤ N) (c : ℝ) (hc : 0 < c) (hlarge : Real.exp (10 * c) < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N c < beta) :
    (∀ x ∈ ({alpha N c, beta} : Finset ℝ), ∀ y ∈ ({alpha N c, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedKernel N (line x p.1) (line y p.2)) 2 volume) ∧
    RepresentsKernel ha N (weightedKernel N) (residualOperator ha N) ∧
    Nonempty (SpectralData (residualOperator ha N)) ∧
    (∀ (h : HardySpace (alpha N c) beta) (s : ℂ), s ∈ strip (alpha N c) beta →
      Integrable (fun t : ℝ => weightedKernel N s (line (alpha N c) t) *
        (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => weightedKernel N s (line beta t) *
        (boundaryTraces ha h).2 t))  := by
  have ha0 := alpha_pos_at N hN4 c hc
  obtain ⟨L,Z,hL,hZ,hlog,hζ⟩ := arithmeticKernel_growth_inputs_at (alpha N c) N ha0 hN4 hGRH ha
  obtain ⟨hK,hcol⟩ := weightedKernel_inputs_of_growth_at (alpha N c) N ha0 hN4 hGRH ha L Z hL hZ hlog hζ
  have hs := residualOperator_spec_at (alpha N c) N ha0 hN4 hGRH ha
  exact ⟨hK,hs.2.1,hs.2.2.2.2.2.1,
    kernelAction_integrable_of_hardyColumns ha (weightedKernel N) (weightedKernel_hermitian N) hcol⟩

end ConditionalGoldbach
