module

public import ConditionalGoldbach.Proofs.SpectralModelGrowth
public import ConditionalGoldbach.Proofs.WeightedComponentKernel
public import ConditionalGoldbach.Proofs.SpectralTraceBounds

/-! Uniform Hilbert--Schmidt estimates for the genuine model operator. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma weightedAnalyticKernel_inputs_at {a : ℝ} (ha0 : 0 < a) (ha : a < beta)
    (F : ℂ → ℂ → ℂ) (hF : DifferentiableOn ℂ (Function.uncurry F) analyticDomain)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s z : ℂ, s.re ∈ Icc a beta → z.re ∈ Icc a beta →
      ‖F s (conj z)‖ ≤ C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ)) :
    (∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedAnalyticKernel F (line x p.1) (line y p.2)) 2 volume) ∧
      HasHardyKernelColumns ha (weightedAnalyticKernel F) := by
  have hsub {s z : ℂ} (hs : s.re ∈ Icc a beta) (hz : z.re ∈ Icc a beta) :
      (s, conj z) ∈ analyticDomain :=
    ⟨ha0.trans_le hs.1, hs.2.trans_lt (by norm_num [beta]),
      by simpa using ha0.trans_le hz.1, by simpa using hz.2.trans_lt (by norm_num [beta] : beta < 3 / 2)⟩
  have hd := weightedAnalyticKernel_conj_differentiableOn F hF
  have hc : ContinuousOn (Function.uncurry (weightedAnalyticKernel F))
      {p : ℂ × ℂ | p.1.re ∈ Icc a beta ∧ p.2.re ∈ Icc a beta} := by
    have hj : ContinuousOn (fun p : ℂ × ℂ => weightedAnalyticKernel F p.1 (conj (conj p.2)))
        {p : ℂ × ℂ | p.1.re ∈ Icc a beta ∧ p.2.re ∈ Icc a beta} :=
      hd.continuousOn.comp (f := fun p : ℂ × ℂ => (p.1, conj p.2)) (by fun_prop)
        (fun p hp => hsub hp.1 hp.2)
    change ContinuousOn (fun p : ℂ × ℂ => weightedAnalyticKernel F p.1 p.2) _
    simpa only [Complex.conj_conj] using hj
  have hhol (z : ℂ) (hz : z.re ∈ Icc a beta) :
      DifferentiableOn ℂ (fun s => weightedAnalyticKernel F s z) (strip a beta) := by
    intro s hs
    have hp := hsub ⟨hs.1.le, hs.2.le⟩ hz
    have hj := hd.differentiableAt (analyticDomain_isOpen.mem_nhds hp)
    have hh := DifferentiableAt.comp (g := fun p : ℂ × ℂ => weightedAnalyticKernel F p.1 (conj p.2))
      (f := fun w : ℂ => (w, conj z)) s hj (by fun_prop)
    simpa only [Function.comp_def, Complex.conj_conj] using hh.differentiableWithinAt (s := strip a beta)
  exact hardyKernel_inputs_of_power_bound ha (weightedAnalyticKernel F) hc hhol
    (16 * C ^ 2) (by positivity)
    (weightedAnalyticKernel_power_bound ha0.le F C hC hbound)

lemma boundaryKernelSquareIntegral_power_bound {a b : ℝ} (hab : a < b)
    (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ∀ v t : ℝ,
      ‖K (line x v) (line y t)‖ ^ 2 ≤
        C * (1 + |v|)^(-(3 / 2 : ℝ)) * (1 + |t|)^(-(3 / 2 : ℝ))) :
    BoundaryKernelSquareIntegral a b K ≤
      4 * C * (∫ t : ℝ, (1 + |t|)^(-(3 / 2 : ℝ)))^2 := by
  let d : ℝ → ℝ := fun t => (1 + |t|)^(-(3 / 2 : ℝ))
  have hd : Integrable (fun p : ℝ × ℝ => C * d p.1 * d p.2) volume := by
    simpa only [smul_eq_mul, Measure.volume_eq_prod] using
      (hardy_decay_integrable.const_mul C).smul_prod hardy_decay_integrable
  have hi (x : ℝ) (hx : x ∈ ({a, b} : Finset ℝ)) (y : ℝ) (hy : y ∈ ({a, b} : Finset ℝ)) :
      (∫ t : ℝ, ∫ u : ℝ, ‖K (line x t) (line y u)‖^2) ≤ C * (∫ t, d t)^2 := by
    have hxi : x ∈ Icc a b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
    have hyi : y ∈ Icc a b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
    calc
      _ = ∫ p : ℝ × ℝ, ‖K (line x p.1) (line y p.2)‖^2 := by
        simpa only [Measure.volume_eq_prod] using (integral_prod _ (hK x hx y hy).norm.integrable_sq).symm
      _ ≤ ∫ p : ℝ × ℝ, C * d p.1 * d p.2 := by
        apply integral_mono (hK x hx y hy).norm.integrable_sq hd
        intro p
        exact hbound x hxi y hyi p.1 p.2
      _ = C * (∫ t, d t)^2 := by
        rw [Measure.volume_eq_prod, integral_prod_mul (fun v : ℝ => C * d v) d, integral_const_mul]
        ring
  unfold BoundaryKernelSquareIntegral
  calc
    _ ≤ ∑ x ∈ ({a, b} : Finset ℝ), ∑ y ∈ ({a, b} : Finset ℝ), C * (∫ t, d t)^2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.sum_le_sum (fun y hy => hi x hx y hy)
    _ = _ := by simp [Finset.sum_pair hab.ne, d]; ring

/-- The model operator has a uniform inverse-square Hilbert--Schmidt bound on every admissible strip. -/
theorem modelOperator_uniform_hs_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∀ ha : a < beta,
      ∀ N : ℕ, ∀ (_ : NeZero N),
      IsHilbertSchmidt (modelOperator ha N) ∧ hsNorm (modelOperator ha N) ≤ C * (a⁻¹)^2 := by
  obtain ⟨B, hB, hmodel⟩ := continuedModel_uniform_power_bound
  let J : ℝ := ∫ t : ℝ, (1 + |t|)^(-(3 / 2 : ℝ))
  refine ⟨8 * B * (|J| + 1), by positivity, ?_⟩
  intro a ha0 ha N hNZ
  let := hNZ
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  let Q := B * (a⁻¹)^2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hbound := hmodel a ha0 ha N hN
  obtain ⟨hK, hcol⟩ := weightedAnalyticKernel_inputs_at ha0 ha (continuedModel N)
    (continuedModel_differentiableOn N hN) Q hQ hbound
  have hherm : HermitianKernel (weightedAnalyticKernel (continuedModel N)) := by
    apply weightedAnalyticKernel_hermitian
    intro s z
    rw [continuedModel_conj, Complex.conj_conj, continuedModel_symmetric]
  obtain ⟨_, _, _, hHilbertSchmidt, _, _, hSquareIntegral, _⟩ :=
    kernelOperator_spec_of_hardyColumns ha N _ hherm hK hcol
  have hhs : IsHilbertSchmidt (modelOperator ha N) := hHilbertSchmidt
  have he : hsNorm (modelOperator ha N)^2 =
      BoundaryKernelSquareIntegral a beta (weightedAnalyticKernel (continuedModel N)) :=
    hSquareIntegral
  refine ⟨hhs, ?_⟩
  have henergy := boundaryKernelSquareIntegral_power_bound ha _ hK (16 * Q^2) (by positivity)
    (weightedAnalyticKernel_power_bound ha0.le (continuedModel N) Q hQ hbound)
  rw [← he] at henergy
  apply (sq_le_sq₀ (hsNorm_nonneg _) (by positivity)).mp
  have hI : J^2 ≤ (|J| + 1)^2 := by nlinarith [sq_abs J, abs_nonneg J]
  calc
    hsNorm (modelOperator ha N)^2 ≤ 4 * (16 * Q^2) * J^2 := henergy
    _ ≤ 4 * (16 * Q^2) * (|J| + 1)^2 := by gcongr
    _ = _ := by dsimp [Q]; ring

end ConditionalGoldbach
