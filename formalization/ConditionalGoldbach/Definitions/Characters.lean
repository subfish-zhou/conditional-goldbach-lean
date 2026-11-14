module

public import ConditionalGoldbach.Definitions.Arithmetic
public import ConditionalGoldbach.Definitions.Geometry
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! Characters definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

abbrev Character (N : ℕ) := DirichletCharacter ℂ N

local instance conductorNeZero {N : ℕ} [NeZero N] (χ : Character N) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

def oddCharacters (N : ℕ) [NeZero N] : Finset (Character N) :=
  Finset.univ.filter (fun χ => χ (-1) = -1)

def characterPolynomial {N : ℕ} (χ : Character N) (φ : ℝ → ℝ) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    (mangoldt n : ℂ) * χ n * (φ (n / N) : ℂ)

def characterMoment (N : ℕ) [NeZero N] (φ : ℝ → ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N, ‖characterPolynomial χ φ‖ ^ 2

def GRH (N : ℕ) : Prop :=
  ∀ d : ℕ, ∀ (_ : NeZero d), d ∣ N → ∀ χ : Character d, χ.IsPrimitive →
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.re = 1 / 2

def logDerivative {N : ℕ} [NeZero N] (χ : Character N) (s : ℂ) : ℂ :=
  deriv χ.LFunction (1 / 2 + s) / χ.LFunction (1 / 2 + s)

def characterKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    logDerivative χ s * conj (logDerivative χ (conj z))

def ZeroIndex {d : ℕ} [NeZero d] (χ : Character d) :=
  {p : ℂ × ℕ // 0 < p.1.re ∧ p.1.re < 1 ∧ χ.LFunction p.1 = 0 ∧
    p.2 < analyticOrderNatAt χ.LFunction p.1}

def completedL {d : ℕ} [NeZero d] (χ : Character d) (u : ℂ) : ℂ :=
  (d : ℂ) ^ ((u + 1) / 2) * χ.completedLFunction u

def zeroDifference {d : ℕ} [NeZero d] (χ : Character d) (u u₀ : ℂ) : ℂ :=
  ∑' p : ZeroIndex χ, (1 / (u - p.val.1) - 1 / (u₀ - p.val.1))

def eulerCorrection {N : ℕ} [NeZero N] (χ : Character N) (u : ℂ) : ℂ :=
  ∑ p ∈ N.primeFactors, if ¬p ∣ χ.conductor then
    χ.primitiveCharacter p * (Real.log p : ℂ) /
      ((p : ℂ) ^ u - χ.primitiveCharacter p) else 0

def zeroPoisson {N : ℕ} [NeZero N] (χ : Character N) (x t : ℝ) : ℝ :=
  ∑' p : ZeroIndex χ.primitiveCharacter, x / (x ^ 2 + (t - p.val.1.im) ^ 2)

def averagedLogDerivative (N : ℕ) [NeZero N] (σ : ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    ∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2)

def arithmeticExpansionTerm (N n m : ℕ) (s z : ℂ) : ℂ :=
  if 0 < n ∧ 0 < m ∧ Nat.Coprime (n * m) N then
    (mangoldt n : ℂ) * mangoldt m / ((n : ℂ) ^ (1 / 2 + s) * (m : ℂ) ^ (1 / 2 + z)) *
      ((if (n : ZMod N) = m then 1 else 0) -
        (if (n : ZMod N) = -(m : ZMod N) then 1 else 0)) else 0

def zeroWindow {d : ℕ} [NeZero d] (χ : Character d) (t : ℝ) : Set (ZeroIndex χ) :=
  {p | t ≤ p.val.1.im ∧ p.val.1.im < t + 1}

def poleCoefficient (N : ℕ) [NeZero N] (γ : ℝ) : ℝ :=
  2 / N.totient * ∑ χ ∈ oddCharacters N,
    (analyticOrderNatAt χ.LFunction (line (1 / 2) γ) : ℝ) ^ 2

def pairedZeroSum {N : ℕ} [NeZero N] (χ : Character N) (s : ℂ) : ℂ :=
  ∑' p : ZeroIndex χ.primitiveCharacter,
    (1 / (s - p.val.1.im * I) - 1 / (3 / 2 - p.val.1.im * I))

def zeroMultiplicity {N : ℕ} [NeZero N] (χ : Character N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt χ.LFunction ρ

def perronCutoff (N : ℕ) : ℝ := (N : ℝ) / 2

def smoothedPerronWeight (X : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ Real.sqrt X then 1
  else if (n : ℝ) ≤ X then Real.log (X / n) / Real.log (Real.sqrt X)
  else 0

def smoothedDirichletPolynomial {N : ℕ} (χ : Character N) (X : ℝ) (u : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
    (mangoldt n : ℂ) * χ n * (n : ℂ) ^ (-u) * smoothedPerronWeight X n

def smoothedPerronKernel (X : ℝ) (v : ℂ) : ℂ :=
  ((X : ℂ) ^ v - (Real.sqrt X : ℂ) ^ v) / (v ^ 2 * Real.log (Real.sqrt X))

def logDerivativeEnergy {N : ℕ} [NeZero N] (χ : Character N) (σ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖logDerivative χ (line σ t)‖ ^ 2 / (1 + t ^ 2)

end ConditionalGoldbach
