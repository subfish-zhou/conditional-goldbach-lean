module

public import ConditionalGoldbach.Definitions.HardyTraces
public import ConditionalGoldbach.Definitions.Hilbert
public import ConditionalGoldbach.Definitions.Model
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Operators definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def weightedKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  residual N s (conj z) / ((1 + s) * (1 + conj z))

def kernelAction {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (h : HardySpace a beta) (s : ℂ) : ℂ :=
  (∫ t : ℝ, K s (line a t) * (boundaryTraces ha h).1 t) +
  ∫ t : ℝ, K s (line beta t) * (boundaryTraces ha h).2 t

def RepresentsKernel {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (T : HardySpace a beta →L[ℂ] HardySpace a beta) : Prop :=
  ∀ h s, s ∈ strip a beta → fourierLaplace (T h) s = kernelAction ha N K h s

def kernelOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) : HardySpace a beta →L[ℂ] HardySpace a beta :=
  if h : ∃ T, RepresentsKernel ha N K T then Classical.choose h else 0

def residualOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (weightedKernel N)

def arithmeticOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (fun s z => characterKernel N s (conj z) / ((1 + s) * (1 + conj z)))

def diagonalOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (fun s z => diagonalSeries N (s + conj z) / ((1 + s) * (1 + conj z)))

def modelOperator {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N] :=
  kernelOperator ha N (fun s z => continuedModel N s (conj z) / ((1 + s) * (1 + conj z)))

def functionalValue {a : ℝ} (N : ℕ) (φ : ℝ → ℝ) (σ : ℝ)
    (h : HardySpace a beta) : ℂ :=
  verticalMellin σ (fun s => (N : ℂ) ^ s * mellinWeight φ s * (1 + s) * fourierLaplace h s)

def rieszVector {a : ℝ} (N : ℕ) (φ : ℝ → ℝ) : HardySpace a beta :=
  if h : ∃ v : HardySpace a beta, ∀ f,
      functionalValue N φ sigmaStar f = paperInner f v
  then Classical.choose h else 0

def evaluationVector {a b : ℝ} (s : ℂ) : HardySpace a b :=
  if h : ∃ v : HardySpace a b, ∀ f, fourierLaplace f s = paperInner f v
  then Classical.choose h else 0

def diagonalHardyVector {a : ℝ} (n : ℕ) : HardySpace a beta :=
  if h : ∃ d : HardySpace a beta, ∀ s ∈ strip a beta,
      fourierLaplace d s = diagonalVector n s
  then Classical.choose h else 0

end ConditionalGoldbach
