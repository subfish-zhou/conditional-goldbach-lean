module

public import ConditionalGoldbach.Definitions.Geometry
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Hardy definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

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

def reproducingKernel (a b : ℝ) (s z : ℂ) : ℂ :=
  (4 * ((b - a : ℝ) : ℂ))⁻¹ /
    Complex.sin ((Real.pi : ℂ) * (s + conj z - 2 * a) / (2 * (b - a : ℝ)))

def wirtingerBar (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (deriv (fun x : ℝ => f (s + x)) 0 + I * deriv (fun y : ℝ => f (s + y * I)) 0) / 2

def wirtinger (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (deriv (fun x : ℝ => f (s + x)) 0 - I * deriv (fun y : ℝ => f (s + y * I)) 0) / 2

abbrev BoundaryParameter := Bool × ℝ

def boundaryPoint (a b : ℝ) (p : BoundaryParameter) : ℂ :=
  line (if p.1 then b else a) p.2

def boundaryMeasure : Measure BoundaryParameter :=
  Measure.prod Measure.count (volume : Measure ℝ)

def poissonKernelReal (a t : ℝ) : ℝ := a / (Real.pi * (a ^ 2 + t ^ 2))

def realConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, f u * g (t - u)

def poissonAction (ℓ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  if ℓ = 0 then f else realConvolution (poissonKernelReal ℓ) f

def diagonalVector (n : ℕ) (s : ℂ) : ℂ := (n : ℂ) ^ (-s) / (1 + s)

end ConditionalGoldbach
