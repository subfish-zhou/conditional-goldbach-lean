module

public import ConditionalGoldbach.Definitions.GeometryCore
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Integration along the two vertical sides of a strip. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace ConditionalGoldbach

def boundaryIntegral (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ t : ℝ, f (line a t)) + ∫ t : ℝ, f (line b t)

end ConditionalGoldbach
