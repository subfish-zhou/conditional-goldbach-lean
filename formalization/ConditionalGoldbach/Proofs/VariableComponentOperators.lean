module

public import ConditionalGoldbach.Proofs.ArithmeticComponentOperators
public import ConditionalGoldbach.Proofs.VariableStripOperators
public import ConditionalGoldbach.Proofs.SpectralModelOperator

public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma component_kernel_power_bounds_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta) :
    ∀ F ∈ ([characterKernel N, (fun s z => diagonalSeries N (s + z)), continuedModel N] : List (ℂ → ℂ → ℂ)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s z : ℂ, s.re ∈ Icc (a) beta → z.re ∈ Icc (a) beta →
        ‖F s (conj z)‖ ≤ C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) := by
  obtain ⟨L, Z, hL, hZ, hlog, hζ⟩ := arithmeticKernel_growth_inputs_at a N ha0 hN4 hGRH ha
  intro F hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by have := hN4; omega)
    apply characterKernel_power_bound N (L * (64 * (2 * N) ^ (1 / 4 : ℝ))) (by positivity)
    intro χ hχ s hs
    calc
      _ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2 := hlog χ hχ s hs
      _ ≤ L * ((64 * (2 * N) ^ (1 / 4 : ℝ)) * (1 + |s.im|) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hN1 s.im) hL
      _ = _ := by ring
  · obtain ⟨D, hD, hd⟩ := diagonalSeries_uniform_bound N
      (show 0 < 2 * a by have := ha0; positivity)
    refine ⟨D, hD, ?_⟩
    intro s z hs hz
    apply (hd _ (by simp; linarith [hs.1, hz.1])).trans
    calc
      D = D * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr <;> exact Real.one_le_rpow (by linarith [abs_nonneg s.im, abs_nonneg z.im]) (by norm_num)
  · exact continuedModel_power_bound (ha0) ha N hN4 Z hZ hζ

lemma component_kernel_operator_spec_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta) :
    ∀ F ∈ ([characterKernel N, (fun s z => diagonalSeries N (s + z)), continuedModel N] : List (ℂ → ℂ → ℂ)),
      RepresentsKernel ha N (weightedAnalyticKernel F) (kernelOperator ha N (weightedAnalyticKernel F)) ∧
      IsHilbertSchmidt (kernelOperator ha N (weightedAnalyticKernel F)) ∧
      (∀ (h : HardySpace (a) beta) (s : ℂ), s ∈ strip (a) beta →
        Integrable (fun t : ℝ => weightedAnalyticKernel F s (line (a) t) * (boundaryTraces ha h).1 t) ∧
        Integrable (fun t : ℝ => weightedAnalyticKernel F s (line beta t) * (boundaryTraces ha h).2 t)) := by
  intro F hF
  obtain ⟨C, hC, hbound⟩ := component_kernel_power_bounds_at a N ha0 hN4 hGRH ha F hF
  have hd := component_kernel_differentiableOn N (by have := hN4; omega) hGRH
  have hh := component_kernel_hermitian N
  have hdiff : DifferentiableOn ℂ (Function.uncurry F) analyticDomain := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hF
    rcases hF with rfl|rfl|rfl
    · exact hd.1
    · exact hd.2.1
    · exact hd.2.2
  have hherm : HermitianKernel (weightedAnalyticKernel F) := by
    apply weightedAnalyticKernel_hermitian
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hF
    rcases hF with rfl|rfl|rfl
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  obtain ⟨hbound,hcol⟩ := weightedAnalyticKernel_inputs_at ha0 ha F hdiff C hC hbound
  have hspec := kernelOperator_spec_of_hardyColumns ha N _ hherm hbound hcol
  exact ⟨hspec.1,hspec.2.2.2.1,kernelAction_integrable_of_hardyColumns ha _ hherm hcol⟩

lemma residualOperator_components_at (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0 < a) (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta) :
    residualOperator ha N = arithmeticOperator ha N-diagonalOperator ha N-modelOperator ha N := by
  have hP := component_kernel_operator_spec_at a N ha0 hN4 hGRH ha (characterKernel N) (by simp)
  have hD := component_kernel_operator_spec_at a N ha0 hN4 hGRH ha (fun s z => diagonalSeries N (s+z)) (by simp)
  have hK := component_kernel_operator_spec_at a N ha0 hN4 hGRH ha (continuedModel N) (by simp)
  apply kernelOperator_eq_of_represents ha N
  have hPD := RepresentsKernel.sub_integrable ha N _ _ _ _ hP.1 hD.1 hP.2.2 hD.2.2
  have hi : ∀ (h : HardySpace (a) beta) (s : ℂ), s ∈ strip (a) beta →
      Integrable (fun t : ℝ => (weightedAnalyticKernel (characterKernel N) s (line (a) t) -
        weightedAnalyticKernel (fun u v => diagonalSeries N (u + v)) s (line (a) t)) * (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => (weightedAnalyticKernel (characterKernel N) s (line beta t) -
        weightedAnalyticKernel (fun u v => diagonalSeries N (u + v)) s (line beta t)) * (boundaryTraces ha h).2 t) := by
    intro h s hs
    constructor
    · convert ((hP.2.2 h s hs).1.sub (hD.2.2 h s hs).1) using 1
      funext t
      exact sub_mul _ _ _
    · convert ((hP.2.2 h s hs).2.sub (hD.2.2 h s hs).2) using 1
      funext t
      exact sub_mul _ _ _
  have hPDK := RepresentsKernel.sub_integrable ha N _ _ _ _ hPD hK.1 hi hK.2.2
  convert hPDK using 1
  · funext s z
    simp only [weightedAnalyticKernel, weightedKernel, residual, sub_div]
  · rfl

end ConditionalGoldbach
