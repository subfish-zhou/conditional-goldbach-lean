module

public import ConditionalGoldbach.Definitions.Characters
public import ConditionalGoldbach.Definitions.Hardy
public import ConditionalGoldbach.Definitions.Hilbert
public import ConditionalGoldbach.Definitions.Weights
public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! Experiment definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
attribute [local instance] conductorNeZero

abbrev experimentN : ℕ := 30030

def cutoffPolynomial (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else
    ∑ j ∈ Finset.Icc 7 13, (Nat.choose 13 j : ℝ) * t ^ j * (1 - t) ^ (13 - j)

def wideCutoff (x : ℝ) : ℝ :=
  cutoffPolynomial ((x - 16) / (1000 - 16)) *
    cutoffPolynomial ((experimentN - x - 16) / (1000 - 16))

def wideCompanion (u : ℝ) : ℝ :=
  if u ∈ Ioo (16 / experimentN : ℝ) (1 - 16 / experimentN : ℝ) then
    Real.sqrt (1 - u) * wideCutoff (experimentN * u) /
      Real.sqrt (Real.log (experimentN * u) * Real.log (experimentN * (1 - u))) else 0

def wideWeight (u : ℝ) : ℝ := wideCompanion u / Real.sqrt u

def wideCorrelation : ℝ := goldbach experimentN wideWeight

def unorderedPrimePairs : ℕ := ((Finset.range (experimentN + 1)).filter
  (fun p => p.Prime ∧ (experimentN - p).Prime ∧ p ≤ experimentN - p)).card

def edgeCorrection : ℝ := ∑ p ∈ Finset.range 1000,
  if p.Prime ∧ (experimentN - p).Prime ∧ p ≤ experimentN - p
  then 1 - wideCutoff p ^ 2 else 0

def primePowerCorrection : ℝ :=
  ∑ p ∈ Finset.range (experimentN + 1), ∑ q ∈ Finset.range (experimentN + 1),
    ∑ k ∈ Finset.range (experimentN + 1), ∑ l ∈ Finset.range (experimentN + 1),
      if p.Prime ∧ q.Prime ∧ 0 < k ∧ 0 < l ∧ 2 ≤ max k l ∧
        p ^ k + q ^ l = experimentN ∧ Nat.Coprime (p * q) experimentN
      then wideCutoff (p ^ k) ^ 2 / (k * l : ℕ) else 0

def countingCoefficient (n : ℕ) : ℝ := mangoldt n / Real.sqrt n * wideCompanion (n / experimentN)

def countingIntegral (χ : Character experimentN) : ℂ :=
  verticalMellin 1 (fun s => (experimentN : ℂ) ^ s *
    mellin (fun u => (wideCompanion u : ℂ)) s * logDerivative χ s)

def diagonalCountingMoment : ℝ := ∑ n ∈ Finset.range experimentN,
  if Nat.Coprime n experimentN then countingCoefficient n ^ 2 else 0

def approxSignedMoment (Ihat : Character experimentN → ℂ) : ℝ :=
  (5760 : ℝ)⁻¹ * (∑ χ : Character experimentN, (χ (-1)).re * ‖Ihat χ‖ ^ 2)

def approxDiagonalMoment (Ihat : Character experimentN → ℂ) : ℝ :=
  (5760 : ℝ)⁻¹ * ∑ χ : Character experimentN, ‖Ihat χ‖ ^ 2

def wideModelMass : ℝ := ∫ u in (0 : ℝ)..1, wideWeight u * wideWeight (1 - u)

def wideResidual : ℝ := wideModelMass * singularSeries experimentN - wideCorrelation

def approxPrimeCount (Ihat : Character experimentN → ℂ) : ℝ :=
  (experimentN : ℝ) / 2 * approxSignedMoment Ihat - primePowerCorrection / 2 + edgeCorrection

def countError (Ihat : Character experimentN → ℂ) (ε : ℝ) : ℝ :=
  (experimentN : ℝ) / 2 * (2 * Real.sqrt (approxDiagonalMoment Ihat) * ε + ε ^ 2)

def wideFunctional {a : ℝ} (h : HardySpace a beta) : ℂ :=
  verticalMellin sigmaStar (fun s => (experimentN : ℂ) ^ s *
    mellin (fun u => (wideCompanion u : ℂ)) s * (1 + s) * fourierLaplace h s)

def wideRieszVector : HardySpace (alpha experimentN) beta :=
  if h : ∃ v : HardySpace (alpha experimentN) beta, ∀ f, wideFunctional f = paperInner f v
  then Classical.choose h else 0

def wideMainIntegral : ℝ := singularSeries experimentN *
  ∫ x in (16 : ℝ)..((experimentN : ℝ) / 2),
    wideCutoff x ^ 2 / (Real.log x * Real.log ((experimentN : ℝ) - x))

def HasMomentError (Ihat : Character experimentN → ℂ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ (5760 : ℝ)⁻¹ * ∑ χ : Character experimentN,
    ‖countingIntegral χ - Ihat χ‖ ^ 2 ≤ ε ^ 2

end ConditionalGoldbach
