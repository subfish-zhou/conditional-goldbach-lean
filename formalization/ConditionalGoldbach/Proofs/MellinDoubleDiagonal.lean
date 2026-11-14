module

public import ConditionalGoldbach.Definitions.Model
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-! Diagonalization and factor extraction for double vertical Mellin integrals. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma double_verticalMellin_diagonal (F : ℂ → ℂ → ℂ) (σ : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => F (line σ p.1) (line σ p.2))) :
    verticalMellin σ (fun s => verticalMellin σ (fun z => F s z)) =
      verticalMellin (2*σ) (fun w => verticalMellin σ (fun s => F s (w-s))) := by
  have hline (v t : ℝ) : line (2*σ) t-line σ v = line σ (t-v) := by
    unfold line
    push_cast
    ring
  rw [Measure.volume_eq_prod] at hi
  have hg : Integrable (fun p : ℝ × ℝ => F (line σ p.1) (line σ (p.2-p.1)))
      (volume.prod volume) := (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable hi
  have he : (∫ v : ℝ, ∫ y : ℝ, F (line σ v) (line σ y)) =
      ∫ t : ℝ, ∫ v : ℝ, F (line σ v) (line (2*σ) t-line σ v) := by
    calc
      _ = ∫ v : ℝ, ∫ t : ℝ, F (line σ v) (line σ (t-v)) := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact (integral_sub_right_eq_self (μ := volume) (fun y : ℝ => F (line σ v) (line σ y)) v).symm
      _ = ∫ t : ℝ, ∫ v : ℝ, F (line σ v) (line σ (t-v)) :=
        integral_integral_swap (f := fun v t : ℝ => F (line σ v) (line σ (t-v))) hg
      _ = _ := by simp_rw [hline]
  simp only [verticalMellin, integral_const_mul, he]

/-- Reduce the double model integral to one vertical Mellin integral. The joint
integrability and beta-transform identity are supplied separately by the smooth
weight and finite-regularity constructions. -/
lemma model_double_mellin_eq_single (N : ℕ) (φ : ℝ → ℝ) (σ : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ =>
      mellinWeight φ (line σ p.1) * mellinWeight φ (line σ p.2) *
        continuedDensity N (line σ p.1 + line σ p.2) *
        betaKernel (line σ p.1) (line σ p.2)))
    (hbeta : ∀ w : ℂ, w.re = 2 * σ →
      mellin (fun y => (signedConvolution φ y : ℂ)) w =
        verticalMellin σ (fun s =>
          mellinWeight φ s * mellinWeight φ (w - s) * betaKernel s (w - s))) :
    verticalMellin σ (fun s => verticalMellin σ (fun z =>
      mellinWeight φ s * mellinWeight φ z * continuedDensity N (s + z) * betaKernel s z)) =
    verticalMellin (2 * σ) (fun w =>
      continuedDensity N w * mellin (fun y => (signedConvolution φ y : ℂ)) w) := by
  rw [double_verticalMellin_diagonal _ σ hi]
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let w := line (2 * σ) t
  have hw : w.re = 2 * σ := by simp [w, line]
  have he (s : ℂ) : mellinWeight φ s * mellinWeight φ (w - s) *
      continuedDensity N (s + (w - s)) * betaKernel s (w - s) =
      continuedDensity N w *
        (mellinWeight φ s * mellinWeight φ (w - s) * betaKernel s (w - s)) := by
    rw [add_sub_cancel]
    ring
  change (2 * (Real.pi : ℂ))⁻¹ *
    (∫ u : ℝ, mellinWeight φ (line σ u) * mellinWeight φ (w - line σ u) *
      continuedDensity N (line σ u + (w - line σ u)) *
        betaKernel (line σ u) (w - line σ u)) = _
  simp_rw [he]
  rw [integral_const_mul]
  change (2 * (Real.pi : ℂ))⁻¹ * (continuedDensity N w * _) =
    continuedDensity N w * mellin (fun y => (signedConvolution φ y : ℂ)) w
  rw [hbeta w hw]
  unfold verticalMellin
  ring

end ConditionalGoldbach
