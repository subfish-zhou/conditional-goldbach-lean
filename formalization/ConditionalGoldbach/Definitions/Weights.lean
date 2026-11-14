module

public import ConditionalGoldbach.Definitions.Geometry
public import Mathlib.Analysis.MellinTransform

/-! Weights definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open scoped ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def IsWeight (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.support φ ⊆ Icc (1 / 3) (2 / 3) ∧
  (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, φ u = φ (1 - u)) ∧ φ ≠ 0

def companion (φ : ℝ → ℝ) (u : ℝ) : ℝ := Real.sqrt u * φ u

def derivativeWeight (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  companion φ u - u * deriv (companion φ) u

def weightMass (φ : ℝ → ℝ) : ℝ := ∫ u in (0 : ℝ)..1, φ u ^ 2

def mellinWeight (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellin (fun u => (companion φ u : ℂ)) s

def verticalMellin (σ : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, f (line σ t)

def differenceConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), φ u * φ (u + y)

def sumConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), φ u * φ (y - u)

def signedConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * differenceConvolution φ y - sumConvolution φ y

def normFunctional (N : ℕ) (φ : ℝ → ℝ) (a : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in Ioi (0 : ℝ),
    Real.rpow (N * u) (2 * a) * derivativeWeight φ u ^ 2 /
      (1 + Real.rpow (N * u) (-2 * (beta - a))) / u

def weightEnergy (φ : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in Ioi (0 : ℝ), derivativeWeight φ u ^ 2 / u

def weightIntegral (φ : ℝ → ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), φ u

def functionalIntegrand (N : ℕ) (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ s * mellinWeight φ s * (1 + s)

end ConditionalGoldbach
