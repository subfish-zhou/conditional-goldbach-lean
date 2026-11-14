module

public import ConditionalGoldbach.Definitions.Characters
public import ConditionalGoldbach.Definitions.Weights
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Model definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def diagonalSeries (N : ℕ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, if 0 < n ∧ Nat.Coprime n N then
    (mangoldt n : ℂ) ^ 2 / (n : ℂ) ^ (1 + w) else 0

def densitySeries (N : ℕ) (w : ℂ) : ℂ :=
  ∑' k : ℕ, if 0 < k then (singularSeries (k * N) : ℂ) / (k : ℂ) ^ w else 0

def densityEulerProduct (N : ℕ) (w : ℂ) : ℂ :=
  ∏' p : ℕ, if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
    1 + (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 1

def continuedDensity (N : ℕ) (w : ℂ) : ℂ :=
  singularSeries N * riemannZeta w * densityEulerProduct N w

def betaKernel (s z : ℂ) : ℂ :=
  betaIntegral (1 / 2 - s) (s + z) + betaIntegral (1 / 2 - z) (s + z) -
    betaIntegral (1 / 2 - s) (1 / 2 - z)

def gammaQuotient (s : ℂ) : ℂ :=
  Gamma ((3 / 2 - s) / 2) / Gamma ((3 / 2 + s) / 2)

def betaModel (N : ℕ) (s z : ℂ) : ℂ :=
  (N : ℂ) ^ (-(s + z)) * continuedDensity N (s + z) * betaKernel s z

def continuedModel (N : ℕ) (s z : ℂ) : ℂ :=
  singularSeries N * ((Real.pi : ℂ) / N) ^ (s + z) *
    densityEulerProduct N (s + z) * riemannZeta (1 - s - z) *
    gammaQuotient s * gammaQuotient z

def residual (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  characterKernel N s z - diagonalSeries N (s + z) - continuedModel N s z

def residualIntegral (N : ℕ) [NeZero N] (φ : ℝ → ℝ) (σ : ℝ) : ℂ :=
  verticalMellin σ (fun s => verticalMellin σ (fun z =>
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * residual N s z))

def betaGamma (u v : ℂ) : ℂ := Gamma u * Gamma v / Gamma (u + v)

def baselineProductR (N : ℕ) (w : ℂ) : ℂ :=
  (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-1 - w))) *
  ∏' p : ℕ, if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
    1 + (2 * (p : ℂ) ^ (-w) - (p : ℂ) ^ (-2 * w)) / ((p : ℂ) * ((p : ℂ) - 2))
  else 1

end ConditionalGoldbach
