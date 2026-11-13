import Mathlib
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-! Audited foundational definitions, preceding the Hardy trace construction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
abbrev Character (N : ℕ) := DirichletCharacter ℂ N

local instance conductorNeZero {N : ℕ} [NeZero N] (χ : Character N) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

abbrev mangoldt := ArithmeticFunction.vonMangoldt

abbrev prime (n : ℕ) := Nat.Prime n

def IsWeight (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.support φ ⊆ Icc (1 / 3) (2 / 3) ∧
  (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, φ u = φ (1 - u)) ∧ φ ≠ 0

def companion (φ : ℝ → ℝ) (u : ℝ) : ℝ := Real.sqrt u * φ u

def derivativeWeight (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  companion φ u - u * deriv (companion φ) u

def weightMass (φ : ℝ → ℝ) : ℝ := ∫ u in (0 : ℝ)..1, φ u ^ 2

def C2 : ℝ := MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct

def singularSeries (N : ℕ) : ℝ :=
  2 * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N

def goldbach (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    if 0 < n ∧ n < N ∧ Nat.Coprime (n * (N - n)) N then
      mangoldt n * mangoldt (N - n) * φ (n / N) * φ ((N - n : ℕ) / N)
    else 0

def diagonalMoment (N : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    if Nat.Coprime n N then (mangoldt n) ^ 2 * φ (n / N) ^ 2 else 0

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

def analyticDomain : Set (ℂ × ℂ) :=
  {p | 0 < p.1.re ∧ p.1.re < 3 / 2 ∧ 0 < p.2.re ∧ p.2.re < 3 / 2}

def betaDomain : Set (ℂ × ℂ) :=
  {p | p.1.re < 1 / 2 ∧ p.2.re < 1 / 2 ∧ 0 < (p.1 + p.2).re}

def alpha (N : ℕ) (c : ℝ := 1) : ℝ := c / Real.log N

def beta : ℝ := 1 / 8

def sigmaStar : ℝ := 1 / 9

def width (a : ℝ) : ℝ := beta - a

def strip (a b : ℝ) : Set ℂ := {s | a < s.re ∧ s.re < b}

def line (x t : ℝ) : ℂ := (x : ℂ) + t * I

def boundaryIntegral (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ t : ℝ, f (line a t)) + ∫ t : ℝ, f (line b t)

def mellinWeight (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellin (fun u => (companion φ u : ℂ)) s

def verticalMellin (σ : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, f (line σ t)

def residualIntegral (N : ℕ) [NeZero N] (φ : ℝ → ℝ) (σ : ℝ) : ℂ :=
  verticalMellin σ (fun s => verticalMellin σ (fun z =>
    (N : ℂ) ^ (s + z) * mellinWeight φ s * mellinWeight φ z * residual N s z))

def differenceConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), φ u * φ (u + y)

def sumConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), φ u * φ (y - u)

def signedConvolution (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * differenceConvolution φ y - sumConvolution φ y

def hardyWeight (a b τ : ℝ) : ℝ := Real.exp (2 * a * τ) + Real.exp (2 * b * τ)

def hardyMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (fun τ => ENNReal.ofReal (hardyWeight a b τ))

abbrev HardySpace (a b : ℝ) := Lp ℂ 2 (hardyMeasure a b)

def fourierLaplace {a b : ℝ} (ψ : HardySpace a b) (s : ℂ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * ∫ τ : ℝ, ψ τ * Complex.exp (s * τ)

def IsRawHardy (a b : ℝ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (strip a b) ∧
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < (b - a) / 2 →
      Integrable (fun t : ℝ => ‖f (line (a + ε) t)‖ ^ 2 +
        ‖f (line (b - ε) t)‖ ^ 2) ∧
      (∫ t : ℝ, ‖f (line (a + ε) t)‖ ^ 2 + ‖f (line (b - ε) t)‖ ^ 2) ≤ C

def rawHardyNormSq (a b : ℝ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ ε : ℝ, 0 < ε ∧ ε < (b - a) / 2 ∧
    r = ∫ t : ℝ, ‖f (line (a + ε) t)‖ ^ 2 + ‖f (line (b - ε) t)‖ ^ 2}

end ConditionalGoldbach
