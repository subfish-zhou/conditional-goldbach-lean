module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Geometry definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

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

def pointDistance (a b : ℝ) (s : ℂ) : ℝ := min (s.re - a) (b - s.re)

def referenceLine (N : ℕ) : ℝ := 2 / Real.log N

end ConditionalGoldbach
