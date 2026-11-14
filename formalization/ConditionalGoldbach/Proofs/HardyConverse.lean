module

public import ConditionalGoldbach.Proofs.HardyGaussianRepresentation
public import ConditionalGoldbach.Proofs.HardyWeakLimit

/-! The full strip Paley–Wiener theorem, including surjectivity from the original raw Hardy condition.
The inverse direction uses Gaussian regularization, contour shifting, Fourier inversion, Fatou,
and weak compactness. No boundary regularity or distributional identity is assumed. -/
public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma rawHardy_fourierLaplace_exists {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : IsRawHardy a b f) :
    ∃ ψ : HardySpace a b, ∀ s ∈ strip a b, fourierLaplace ψ s = f s := by
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hε : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hε' : ∀ n, ε n ≤ 1 := by
    intro n
    dsimp [ε]
    apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).const_div_atTop 1
  let ψ : ℕ → HardySpace a b := fun n => hardyGaussianVector hab hf (hε n) (hε' n)
  obtain ⟨C, hC⟩ := hardyGaussianVector_uniform_norm_bound hab hf
  have hb : ∀ n, ‖ψ n‖ ≤ C := fun n => hC (ε n) (hε n) (hε' n)
  have hlim : ∀ s ∈ strip a b, Tendsto (fun n => fourierLaplace (ψ n) s) atTop (𝓝 (f s)) := by
    intro s hs
    have h := ((hεlim.ofReal.mul_const (s ^ 2)).cexp).const_mul (f s)
    have he : (fun n => fourierLaplace (ψ n) s) =
        fun n => f s * Complex.exp ((ε n : ℂ) * s ^ 2) := by
      funext n
      exact hardyGaussianVector_representation hab hf (hε n) (hε' n) hs
    rw [he]
    simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] using h
  obtain ⟨χ, hχ, hχspec⟩ := hardy_bounded_pointwise_limit ψ hb f hlim
  exact ⟨χ, hχspec⟩

theorem lemma_5_2 (a b : ℝ) (hab : a < b) :
    (∀ ψ : HardySpace a b, IsRawHardy a b (fourierLaplace ψ) ∧
      rawHardyNormSq a b (fourierLaplace ψ) = ‖ψ‖ ^ 2 ∧
      ‖ψ‖ ^ 2 = ‖(boundaryTraces hab ψ).1‖ ^ 2 + ‖(boundaryTraces hab ψ).2‖ ^ 2) ∧
    (∀ f : ℂ → ℂ, IsRawHardy a b f →
      ∃! ψ : HardySpace a b, ∀ s ∈ strip a b, fourierLaplace ψ s = f s) := by
  refine ⟨lemma_5_2_forward a b hab, ?_⟩
  intro f hf
  obtain ⟨ψ, hψ⟩ := rawHardy_fourierLaplace_exists hab hf
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  apply fourierLaplace_injective_strip hab
  intro s hs
  exact (hχ s hs).trans (hψ s hs).symm

end ConditionalGoldbach
