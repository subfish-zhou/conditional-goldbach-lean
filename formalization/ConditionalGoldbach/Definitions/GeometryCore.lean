module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic

/-! Strip geometry and scale parameters, independent of integration and Hardy spaces. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open Set Complex
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

def pointDistance (a b : ℝ) (s : ℂ) : ℝ := min (s.re - a) (b - s.re)

def referenceLine (N : ℕ) : ℝ := 2 / Real.log N

end ConditionalGoldbach
