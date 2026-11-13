import ConditionalGoldbach.Proofs.WeightedComponentKernel
import ConditionalGoldbach.Proofs.HardyArithmeticTheorems

/-! The three actual component operators and the exact residual decomposition. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma component_kernel_hermitian (N : ℕ) [NeZero N] :
    HermitianKernel (fun s z => characterKernel N s (conj z)) ∧
    HermitianKernel (fun s z => diagonalSeries N (s + conj z)) ∧
    HermitianKernel (fun s z => continuedModel N s (conj z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s z
    rw [characterKernel_conjugation, Complex.conj_conj, characterKernel_symmetric]
  · intro s z
    rw [diagonalSeries_conj, map_add, Complex.conj_conj, add_comm]
  · intro s z
    rw [continuedModel_conj, Complex.conj_conj, continuedModel_symmetric]

lemma component_kernel_differentiableOn (N : ℕ) [NeZero N] (hN : 0 < N) (hGRH : GRH N) :
    DifferentiableOn ℂ (Function.uncurry (characterKernel N)) analyticDomain ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => diagonalSeries N (p.1 + p.2)) analyticDomain ∧
    DifferentiableOn ℂ (Function.uncurry (continuedModel N)) analyticDomain := by
  refine ⟨(characterKernel_differentiableOn_of_GRH hGRH).mono
    (fun p hp => ⟨hp.1, hp.2.2.1⟩), ?_, continuedModel_differentiableOn N hN⟩
  intro p hp
  have hs : 0 < (p.1 + p.2).re := by simp; linarith [hp.1, hp.2.2.1]
  exact ((diagonalSeries_differentiableAt N hs).comp p
    (show DifferentiableAt ℂ (fun q : ℂ × ℂ => q.1 + q.2) p by fun_prop)).differentiableWithinAt

lemma component_kernel_power_bounds (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    ∀ F ∈ ([characterKernel N, (fun s z => diagonalSeries N (s + z)), continuedModel N] : List (ℂ → ℂ → ℂ)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s z : ℂ, s.re ∈ Icc (alpha N) beta → z.re ∈ Icc (alpha N) beta →
        ‖F s (conj z)‖ ≤ C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) := by
  obtain ⟨L, Z, hL, hZ, hlog, hζ⟩ := arithmeticKernel_growth_inputs N hlarge hGRH ha
  intro F hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by have := (large_parameters hlarge).1; omega)
    apply characterKernel_power_bound N (L * (64 * (2 * N) ^ (1 / 4 : ℝ))) (by positivity)
    intro χ hχ s hs
    calc
      _ ≤ L * Real.log (N * (|s.im| + 2)) ^ 2 := hlog χ hχ s hs
      _ ≤ L * ((64 * (2 * N) ^ (1 / 4 : ℝ)) * (1 + |s.im|) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hN1 s.im) hL
      _ = _ := by ring
  · obtain ⟨D, hD, hd⟩ := diagonalSeries_uniform_bound N
      (show 0 < 2 * alpha N by have := large_alpha_pos hlarge; positivity)
    refine ⟨D, hD, ?_⟩
    intro s z hs hz
    apply (hd _ (by simp; linarith [hs.1, hz.1])).trans
    calc
      D = D * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr <;> exact Real.one_le_rpow (by linarith [abs_nonneg s.im, abs_nonneg z.im]) (by norm_num)
  · exact continuedModel_power_bound (large_alpha_pos hlarge) ha N (large_parameters hlarge).1 Z hZ hζ

lemma component_kernel_operator_spec (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    ∀ F ∈ ([characterKernel N, (fun s z => diagonalSeries N (s + z)), continuedModel N] : List (ℂ → ℂ → ℂ)),
      RepresentsKernel ha N (weightedAnalyticKernel F) (kernelOperator ha N (weightedAnalyticKernel F)) ∧
      IsHilbertSchmidt (kernelOperator ha N (weightedAnalyticKernel F)) ∧
      (∀ (h : HardySpace (alpha N) beta) (s : ℂ), s ∈ strip (alpha N) beta →
        Integrable (fun t : ℝ => weightedAnalyticKernel F s (line (alpha N) t) * (boundaryTraces ha h).1 t) ∧
        Integrable (fun t : ℝ => weightedAnalyticKernel F s (line beta t) * (boundaryTraces ha h).2 t)) := by
  intro F hF
  obtain ⟨C, hC, hbound⟩ := component_kernel_power_bounds N hlarge hGRH ha F hF
  have hd := component_kernel_differentiableOn N (by have := (large_parameters hlarge).1; omega) hGRH
  have hh := component_kernel_hermitian N
  apply weightedAnalyticKernel_operator_spec N hlarge ha F _ _ C hC hbound
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    · exact hd.1
    · exact hd.2.1
    · exact hd.2.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2

lemma RepresentsKernel.sub_integrable {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K L : ℂ → ℂ → ℂ) (T S : HardySpace a beta →L[ℂ] HardySpace a beta)
    (hT : RepresentsKernel ha N K T) (hS : RepresentsKernel ha N L S)
    (hK : ∀ (h : HardySpace a beta) (s : ℂ), s ∈ strip a beta →
      Integrable (fun t : ℝ => K s (line a t) * (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => K s (line beta t) * (boundaryTraces ha h).2 t))
    (hL : ∀ (h : HardySpace a beta) (s : ℂ), s ∈ strip a beta →
      Integrable (fun t : ℝ => L s (line a t) * (boundaryTraces ha h).1 t) ∧
      Integrable (fun t : ℝ => L s (line beta t) * (boundaryTraces ha h).2 t)) :
    RepresentsKernel ha N (fun s z => K s z - L s z) (T - S) := by
  intro h s hs
  change fourierLaplace (T h - S h) s = _
  rw [← hardyEvaluationFunctional_apply hs, map_sub,
    hardyEvaluationFunctional_apply hs, hardyEvaluationFunctional_apply hs, hT h s hs, hS h s hs]
  unfold kernelAction
  simp only [sub_mul]
  rw [integral_sub (hK h s hs).1 (hL h s hs).1,
    integral_sub (hK h s hs).2 (hL h s hs).2]
  ring

theorem proposition_6_5_components_spec (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    let α := alpha N
    let P := arithmeticOperator ha N
    let D := diagonalOperator ha N
    let K := modelOperator ha N
    let κP := fun s z : ℂ => characterKernel N s (conj z) / ((1 + s) * (1 + conj z))
    let κD := fun s z : ℂ => diagonalSeries N (s + conj z) / ((1 + s) * (1 + conj z))
    let κK := fun s z : ℂ => continuedModel N s (conj z) / ((1 + s) * (1 + conj z))
    RepresentsKernel ha N κP P ∧ RepresentsKernel ha N κD D ∧ RepresentsKernel ha N κK K ∧
    (∀ κ ∈ ([κP, κD, κK] : List (ℂ → ℂ → ℂ)),
      ∀ (h : HardySpace α beta) (s : ℂ), s ∈ strip α beta →
        Integrable (fun t : ℝ => κ s (line α t) * (boundaryTraces ha h).1 t) ∧
        Integrable (fun t : ℝ => κ s (line beta t) * (boundaryTraces ha h).2 t)) ∧
    residualOperator ha N = P - D - K := by
  have hP := component_kernel_operator_spec N hlarge hGRH ha (characterKernel N) (by simp)
  have hD := component_kernel_operator_spec N hlarge hGRH ha (fun s z => diagonalSeries N (s + z)) (by simp)
  have hK := component_kernel_operator_spec N hlarge hGRH ha (continuedModel N) (by simp)
  refine ⟨hP.1, hD.1, hK.1, ?_, ?_⟩
  · intro κ hκ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl | rfl
    · exact hP.2.2
    · exact hD.2.2
    · exact hK.2.2
  · apply kernelOperator_eq_of_represents ha N
    have hPD := RepresentsKernel.sub_integrable ha N _ _ _ _ hP.1 hD.1 hP.2.2 hD.2.2
    have hi : ∀ (h : HardySpace (alpha N) beta) (s : ℂ), s ∈ strip (alpha N) beta →
        Integrable (fun t : ℝ => (weightedAnalyticKernel (characterKernel N) s (line (alpha N) t) -
          weightedAnalyticKernel (fun u v => diagonalSeries N (u + v)) s (line (alpha N) t)) * (boundaryTraces ha h).1 t) ∧
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
