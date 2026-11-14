module

public import ConditionalGoldbach.Proofs.ArithmeticKernelRealization

/-! Reusable weighted component kernels on the same Hardy strip. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

def weightedAnalyticKernel (F : ℂ → ℂ → ℂ) (s z : ℂ) : ℂ :=
  F s (conj z) / ((1 + s) * (1 + conj z))

lemma weightedAnalyticKernel_power_bound {a b : ℝ} (ha : 0 ≤ a)
    (F : ℂ → ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ s z : ℂ, s.re ∈ Icc a b → z.re ∈ Icc a b →
      ‖F s (conj z)‖ ≤
        C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ)) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ∀ v t : ℝ,
      ‖weightedAnalyticKernel F (line x v) (line y t)‖ ^ 2 ≤
        (16 * C ^ 2) * (1 + |v|) ^ (- (3 / 2 : ℝ)) *
          (1 + |t|) ^ (- (3 / 2 : ℝ)) := by
  intro x hx y hy v t
  have hv0 : 0 < 1 + |v| := by positivity
  have ht0 : 0 < 1 + |t| := by positivity
  have hvl := one_add_line_norm_lower (ha.trans hx.1) v
  have htl := one_add_line_norm_lower (ha.trans hy.1) t
  have hR' : ‖F (line x v) (conj (line y t))‖ ≤
      C * (1 + |v|) ^ (1 / 4 : ℝ) * (1 + |t|) ^ (1 / 4 : ℝ) := by
    simpa [line] using hR (line x v) (line y t) (by simpa [line] using hx) (by simpa [line] using hy)
  have hnorm : ‖weightedAnalyticKernel F (line x v) (line y t)‖ ≤
      (4 * C) * (1 + |v|) ^ (- (3 / 4 : ℝ)) * (1 + |t|) ^ (- (3 / 4 : ℝ)) := by
    rw [weightedAnalyticKernel, norm_div, norm_mul]
    have hc : ‖1 + conj (line y t)‖ = ‖1 + line y t‖ := by
      simpa only [map_add, map_one] using Complex.norm_conj (1 + line y t)
    rw [hc]
    calc
      _ ≤ (C * (1 + |v|) ^ (1 / 4 : ℝ) * (1 + |t|) ^ (1 / 4 : ℝ)) /
          (((1 + |v|) / 2) * ((1 + |t|) / 2)) :=
        div_le_div₀ (by positivity) hR' (by positivity)
          (mul_le_mul hvl htl (by positivity) (norm_nonneg _))
      _ = _ := by
        have hv : (1 + |v|) ^ (- (3 / 4 : ℝ)) =
            (1 + |v|) ^ (1 / 4 : ℝ) / (1 + |v|) := by
          rw [show - (3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub hv0, Real.rpow_one]
        have ht : (1 + |t|) ^ (- (3 / 4 : ℝ)) =
            (1 + |t|) ^ (1 / 4 : ℝ) / (1 + |t|) := by
          rw [show - (3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub ht0, Real.rpow_one]
        rw [hv, ht]
        field_simp; ring
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have hp (u : ℝ) (hu : 0 < 1 + |u|) :
      ((1 + |u|) ^ (- (3 / 4 : ℝ))) ^ 2 = (1 + |u|) ^ (- (3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    norm_num
  simpa only [mul_pow, hp v hv0, hp t ht0, show (4 : ℝ)^2 = 16 by norm_num] using hsq


lemma weightedAnalyticKernel_hermitian (F : ℂ → ℂ → ℂ)
    (hF : HermitianKernel (fun s z => F s (conj z))) :
    HermitianKernel (weightedAnalyticKernel F) := by
  intro s z
  unfold weightedAnalyticKernel
  rw [map_div₀, map_mul, map_add, map_add, map_one, Complex.conj_conj, ← hF s z]
  congr 1
  ring

lemma weightedAnalyticKernel_conj_differentiableOn (F : ℂ → ℂ → ℂ)
    (hF : DifferentiableOn ℂ (Function.uncurry F) analyticDomain) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => weightedAnalyticKernel F p.1 (conj p.2)) analyticDomain := by
  intro p hp
  have hs : (1 : ℂ) + p.1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith [hp.1]
  have hz : (1 : ℂ) + p.2 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith [hp.2.2.1]
  simp only [weightedAnalyticKernel, Complex.conj_conj]
  have hd : DifferentiableWithinAt ℂ (fun q : ℂ × ℂ => (1 + q.1) * (1 + q.2)) analyticDomain p := by fun_prop
  have hf : DifferentiableWithinAt ℂ (fun q : ℂ × ℂ => F q.1 q.2) analyticDomain p := hF p hp
  simpa only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using!
    hf.mul (hd.inv (mul_ne_zero hs hz))

lemma weightedAnalyticKernel_inputs (N : ℕ) (hlarge : Real.exp 10 < (N : ℝ)) (ha : alpha N < beta)
    (F : ℂ → ℂ → ℂ) (hF : DifferentiableOn ℂ (Function.uncurry F) analyticDomain)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s z : ℂ, s.re ∈ Icc (alpha N) beta → z.re ∈ Icc (alpha N) beta →
      ‖F s (conj z)‖ ≤ C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ)) :
    (∀ x ∈ ({alpha N, beta} : Finset ℝ), ∀ y ∈ ({alpha N, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => weightedAnalyticKernel F (line x p.1) (line y p.2)) 2 volume) ∧
      HasHardyKernelColumns ha (weightedAnalyticKernel F) := by
  have hd := weightedAnalyticKernel_conj_differentiableOn F hF
  have hc : ContinuousOn (Function.uncurry (weightedAnalyticKernel F))
      {p : ℂ × ℂ | p.1.re ∈ Icc (alpha N) beta ∧ p.2.re ∈ Icc (alpha N) beta} := by
    have hj : ContinuousOn (fun p : ℂ × ℂ => weightedAnalyticKernel F p.1 (conj (conj p.2)))
        {p : ℂ × ℂ | p.1.re ∈ Icc (alpha N) beta ∧ p.2.re ∈ Icc (alpha N) beta} := by
      apply hd.continuousOn.comp (f := fun p : ℂ × ℂ => (p.1, conj p.2)) (by fun_prop)
      intro p hp
      exact large_closed_strip_subset hlarge ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
    change ContinuousOn (fun p : ℂ × ℂ => weightedAnalyticKernel F p.1 p.2) _
    simpa only [Complex.conj_conj] using hj
  have hhol (z : ℂ) (hz : z.re ∈ Icc (alpha N) beta) :
      DifferentiableOn ℂ (fun s => weightedAnalyticKernel F s z) (strip (alpha N) beta) := by
    intro s hs
    have hp : (s, conj z) ∈ analyticDomain := large_closed_strip_subset hlarge
      ⟨hs.1.le, hs.2.le, hz.1, hz.2⟩
    have hj := hd.differentiableAt (analyticDomain_isOpen.mem_nhds hp)
    have hh := DifferentiableAt.comp (g := fun p : ℂ × ℂ => weightedAnalyticKernel F p.1 (conj p.2))
      (f := fun w : ℂ => (w, conj z)) s hj (by fun_prop)
    simpa only [Function.comp_def, Complex.conj_conj] using hh.differentiableWithinAt (s := strip (alpha N) beta)
  exact hardyKernel_inputs_of_power_bound ha (weightedAnalyticKernel F) hc hhol
    (16 * C ^ 2) (by positivity)
    (weightedAnalyticKernel_power_bound (large_alpha_pos hlarge).le F C hC hbound)

lemma weightedAnalyticKernel_operator_spec (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (ha : alpha N < beta)
    (F : ℂ → ℂ → ℂ) (hF : DifferentiableOn ℂ (Function.uncurry F) analyticDomain)
    (hherm : HermitianKernel (fun s z => F s (conj z)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s z : ℂ, s.re ∈ Icc (alpha N) beta → z.re ∈ Icc (alpha N) beta →
      ‖F s (conj z)‖ ≤ C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ)) :
    RepresentsKernel ha N (weightedAnalyticKernel F) (kernelOperator ha N (weightedAnalyticKernel F)) ∧
      IsHilbertSchmidt (kernelOperator ha N (weightedAnalyticKernel F)) ∧
      (∀ (h : HardySpace (alpha N) beta) (s : ℂ), s ∈ strip (alpha N) beta →
        Integrable (fun t : ℝ => weightedAnalyticKernel F s (line (alpha N) t) * (boundaryTraces ha h).1 t) ∧
        Integrable (fun t : ℝ => weightedAnalyticKernel F s (line beta t) * (boundaryTraces ha h).2 t)) := by
  obtain ⟨hK, hcol⟩ := weightedAnalyticKernel_inputs N hlarge ha F hF C hC hbound
  have hsym := weightedAnalyticKernel_hermitian F hherm
  have hspec := kernelOperator_spec_of_hardyColumns ha N (weightedAnalyticKernel F) hsym hK hcol
  exact ⟨hspec.1, hspec.2.2.2.1,
    kernelAction_integrable_of_hardyColumns ha (weightedAnalyticKernel F) hsym hcol⟩

end ConditionalGoldbach
