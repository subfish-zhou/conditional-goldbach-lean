import LiLiuGoldbach.Proofs.HardyKernelColumns
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! A product majorant supplies both the four boundary L² blocks and all closed-strip Hardy columns. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace LiLiuGoldbach16

lemma hardyKernel_inputs_of_majorant {a b : ℝ} (hab : a < b) (K : ℂ → ℂ → ℂ)
    (hc : ContinuousOn (Function.uncurry K)
      {p : ℂ × ℂ | p.1.re ∈ Icc a b ∧ p.2.re ∈ Icc a b})
    (hhol : ∀ s : ℂ, s.re ∈ Icc a b → DifferentiableOn ℂ (fun z => K z s) (strip a b))
    (M : ℝ → ℝ) (hM : Integrable M)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ∀ v t : ℝ,
      ‖K (line x v) (line y t)‖ ^ 2 ≤ M v * M t) :
    (∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume) ∧
      HasHardyKernelColumns hab K := by
  constructor
  · intro x hx y hy
    have hxi : x ∈ Icc a b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
    have hyi : y ∈ Icc a b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
    have hcont : Continuous (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) := by
      apply hc.comp_continuous (show Continuous (fun p : ℝ × ℝ => (line x p.1, line y p.2)) by
        unfold line; fun_prop)
      intro p
      simpa [line] using And.intro hxi hyi
    apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
    have hi : Integrable (fun p : ℝ × ℝ => M p.1 * M p.2) volume := by
      simpa only [smul_eq_mul, Measure.volume_eq_prod] using hM.smul_prod hM
    apply hi.mono' (hcont.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with p
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using hbound x hxi y hyi p.1 p.2
  · apply hardyKernelColumns_of_majorant hab K hhol
    · intro s hs
      exact hc.comp (f := fun z : ℂ => (z, s)) (by fun_prop)
        (by intro z hz; exact ⟨hz, hs⟩)
    · intro s hs
      refine ⟨fun t => M t * M s.im, hM.mul_const _, ?_⟩
      intro x hx t
      have he : line s.re s.im = s := by apply Complex.ext <;> simp [line]
      simpa only [he] using hbound x hx s.re hs t s.im

lemma hardy_decay_integrable : Integrable (fun t : ℝ => (1 + |t|) ^ (- (3 / 2 : ℝ))) := by
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (μ := (volume : Measure ℝ)) (by norm_num :
      (Module.finrank ℝ ℝ : ℝ) < (3 / 2 : ℝ)))

lemma hardyKernel_inputs_of_power_bound {a b : ℝ} (hab : a < b) (K : ℂ → ℂ → ℂ)
    (hc : ContinuousOn (Function.uncurry K)
      {p : ℂ × ℂ | p.1.re ∈ Icc a b ∧ p.2.re ∈ Icc a b})
    (hhol : ∀ s : ℂ, s.re ∈ Icc a b → DifferentiableOn ℂ (fun z => K z s) (strip a b))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ∀ v t : ℝ,
      ‖K (line x v) (line y t)‖ ^ 2 ≤
        C * (1 + |v|) ^ (- (3 / 2 : ℝ)) * (1 + |t|) ^ (- (3 / 2 : ℝ))) :
    (∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume) ∧
      HasHardyKernelColumns hab K := by
  apply hardyKernel_inputs_of_majorant hab K hc hhol
    (fun t => Real.sqrt C * (1 + |t|) ^ (- (3 / 2 : ℝ)))
    (hardy_decay_integrable.const_mul _)
  intro x hx y hy v t
  convert hbound x hx y hy v t using 1
  rw [show Real.sqrt C * (1 + |v|) ^ (- (3 / 2 : ℝ)) *
      (Real.sqrt C * (1 + |t|) ^ (- (3 / 2 : ℝ))) =
      (Real.sqrt C)^2 * (1 + |v|) ^ (- (3 / 2 : ℝ)) * (1 + |t|) ^ (- (3 / 2 : ℝ)) by ring,
    Real.sq_sqrt hC]

end LiLiuGoldbach16
