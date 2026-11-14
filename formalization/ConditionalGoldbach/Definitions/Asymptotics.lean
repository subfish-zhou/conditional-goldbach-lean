module

public import ConditionalGoldbach.Definitions.Geometry
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Asymptotics definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def EvenEventually (P : ℕ → Prop) : Prop := ∃ N₀ : ℕ, ∀ N ≥ N₀, Even N → P N

def EvenTendstoInfinity (h : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, EvenEventually (fun N => B ≤ h N)

def NormallySummableOn {ι X : Type*} [TopologicalSpace X]
    (f : ι → X → ℂ) (U : Set X) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ U →
    (∀ i, BddAbove {r : ℝ | ∃ x ∈ K, r = ‖f i x‖}) ∧
    Summable (fun i => sSup {r : ℝ | ∃ x ∈ K, r = ‖f i x‖})

def HermitianKernel (K : ℂ → ℂ → ℂ) : Prop := ∀ s z, K s z = conj (K z s)

def PositiveKernel (K : ℂ → ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∀ points coefficients : Fin n → ℂ,
    0 ≤ (∑ i, ∑ j, coefficients i * conj (coefficients j) * K (points i) (points j)).re

def BoundaryKernelSquareIntegral (a b : ℝ) (K : ℂ → ℂ → ℂ) : ℝ :=
  ∑ x ∈ ({a, b} : Finset ℝ), ∑ y ∈ ({a, b} : Finset ℝ),
    ∫ t : ℝ, ∫ u : ℝ, ‖K (line x t) (line y u)‖ ^ 2

def CompactUniformLimit {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    (f : ℕ → X → Y) (g : X → Y) : Prop :=
  ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ n₀, ∀ n ≥ n₀, ∀ x ∈ K, ‖f n x - g x‖ < ε

def EvenAsymptotic (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → EvenEventually (fun N => |f N / g N - 1| < ε)

def baselineBound (C : ℝ) (N : ℕ) (a : ℝ) : ℝ := C * (Real.log N ^ 2 + a⁻¹ ^ 2)

def balanceFactor (c : ℝ) : ℝ := Real.exp (2 * c) * (1 + c⁻¹ ^ 2)

def availableNormMajorant (C : ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  C * (Real.log N ^ 2 + a ^ (-2 : ℤ))

end ConditionalGoldbach
