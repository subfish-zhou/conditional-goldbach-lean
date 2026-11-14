module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-! Arithmetic definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

abbrev mangoldt := ArithmeticFunction.vonMangoldt

abbrev prime (n : ℕ) := Nat.Prime n

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

def PrimePairCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime ∧
    (N : ℝ) / 3 ≤ p ∧ (p : ℝ) ≤ 2 * N / 3)).card

def positiveDifferenceFamily (N n m k : ℕ) : Prop :=
  0 < k ∧ m = n + k * N

def negativeDifferenceFamily (N n m k : ℕ) : Prop :=
  0 < k ∧ n = m + k * N

def sumFamily (N n m k : ℕ) : Prop :=
  0 < k ∧ n + m = k * N

def localDensityFactor (p h : ℕ) : ℝ :=
  (1 - (if p ∣ h then 1 else 2) / (p : ℝ)) / (1 - (p : ℝ)⁻¹) ^ 2

end ConditionalGoldbach
