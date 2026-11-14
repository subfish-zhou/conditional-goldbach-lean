module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import ConditionalGoldbach.Proofs.HardyTraceAlgebra

/-! Holomorphy of the Fourier–Laplace representation on its open strip. -/
public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology
namespace ConditionalGoldbach

lemma hardy_derivative_exp_bound (u v δ τ : ℝ) (hδ : 0 < δ) (hu : |u - v| ≤ δ) :
    |τ| * Real.exp (u * τ) ≤
      δ⁻¹ * (Real.exp ((v - 2 * δ) * τ) + Real.exp ((v + 2 * δ) * τ)) := by
  have habs : δ * |τ| ≤ Real.exp (δ * |τ|) := by
    linarith [Real.add_one_le_exp (δ * |τ|)]
  have h := mul_le_mul_of_nonneg_right habs (Real.exp_pos (u * τ)).le
  rw [← Real.exp_add] at h
  have hb : Real.exp (δ * |τ| + u * τ) ≤
      Real.exp ((v - 2 * δ) * τ) + Real.exp ((v + 2 * δ) * τ) := by
    by_cases hτ : 0 ≤ τ
    · rw [abs_of_nonneg hτ]
      apply le_trans (Real.exp_le_exp.mpr ?_) (le_add_of_nonneg_left (Real.exp_pos _).le)
      nlinarith [(abs_le.mp hu).2]
    · rw [abs_of_neg (lt_of_not_ge hτ)]
      apply le_trans (Real.exp_le_exp.mpr ?_) (le_add_of_nonneg_right (Real.exp_pos _).le)
      nlinarith [(abs_le.mp hu).1]
  have hh := le_trans h hb
  calc
    _ = δ⁻¹ * (δ * |τ| * Real.exp (u * τ)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hδ.le)

lemma fourierLaplace_differentiableAt {a b : ℝ} (ψ : HardySpace a b) {s : ℂ}
    (hs : s ∈ strip a b) : DifferentiableAt ℂ (fourierLaplace ψ) s := by
  have hsa : 0 < s.re - a := sub_pos.mpr hs.1
  have hsb : 0 < b - s.re := sub_pos.mpr hs.2
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ a < s.re - 2 * δ ∧ s.re + 2 * δ < b := by
    refine ⟨min (s.re - a) (b - s.re) / 4, by positivity, ?_, ?_⟩
    · have hm := min_le_left (s.re - a) (b - s.re)
      have ha : a < s.re := hs.1
      linarith
    · have hm := min_le_right (s.re - a) (b - s.re)
      have hb : s.re < b := hs.2
      linarith
  let B : ℝ → ℝ := fun τ => δ⁻¹ *
    (Real.exp ((s.re - 2 * δ) * τ) + Real.exp ((s.re + 2 * δ) * τ)) * ‖ψ τ‖
  have hB : Integrable B := by
    have h1 := (hardy_weighted_line_integrable (a := a) (b := b)
      (x := s.re - 2 * δ) ⟨hδa, by linarith [hs.2]⟩ ψ).norm
    have h2 := (hardy_weighted_line_integrable (a := a) (b := b)
      (x := s.re + 2 * δ) ⟨by linarith [hs.1], hδb⟩ ψ).norm
    have h := (h1.add h2).const_mul δ⁻¹
    simpa only [B, Pi.add_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), add_mul, mul_add, mul_assoc] using h
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z : ℂ => fun τ : ℝ => ψ τ * Complex.exp (z * τ))
    (F' := fun z : ℂ => fun τ : ℝ => ψ τ * (Complex.exp (z * τ) * τ))
    (bound := B) (Metric.ball_mem_nhds s hδ)
    (Eventually.of_forall (fun z => (hardySpace_aestronglyMeasurable ψ).mul
      (by fun_prop : Continuous (fun τ : ℝ => Complex.exp (z * τ))).aestronglyMeasurable))
    (fourierLaplace_integrable ψ hs)
    ((hardySpace_aestronglyMeasurable ψ).mul
      (by fun_prop : Continuous (fun τ : ℝ => Complex.exp (s * τ) * τ)).aestronglyMeasurable)
    ?_ hB ?_
  · exact hmain.2.differentiableAt.const_mul _
  · apply Eventually.of_forall
    intro τ z hz
    have hz' : |z.re - s.re| ≤ δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h := (Complex.abs_re_le_norm (z - s)).trans (le_of_lt hz)
      simpa only [Complex.sub_re, dist_eq_norm] using h
    have h := mul_le_mul_of_nonneg_right (hardy_derivative_exp_bound z.re s.re δ τ hδ hz') (norm_nonneg (ψ τ))
    simpa only [B, Pi.add_apply, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      mul_assoc, mul_comm, mul_left_comm] using h
  · exact Eventually.of_forall (fun τ z _ => by
      simpa only [id_eq, one_mul] using
        ((((hasDerivAt_id z).mul_const (τ : ℂ)).cexp).const_mul (ψ τ)))

lemma fourierLaplace_differentiableOn {a b : ℝ} (ψ : HardySpace a b) :
    DifferentiableOn ℂ (fourierLaplace ψ) (strip a b) :=
  fun _ hs => (fourierLaplace_differentiableAt ψ hs).differentiableWithinAt

end ConditionalGoldbach
