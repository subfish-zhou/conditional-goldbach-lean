module

public import ConditionalGoldbach.Definitions.Asymptotics
public import ConditionalGoldbach.Definitions.Operators
public import ConditionalGoldbach.Definitions.Spectral
public import Mathlib.Algebra.Quaternion
public import Mathlib.MeasureTheory.Function.L2Space

/-! Hypotheses definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def RealizationValid (N : ℕ) (a : ℝ) : Prop :=
  Even N ∧ 4 ≤ N ∧ GRH N ∧ 0 < a ∧ a < 1 / 10

def zeroFreeWidth (N : ℕ) (h : ℕ → ℝ) : ℝ :=
  h N ^ 2 * Real.log N ^ 3 / (N * singularSeries N)

def IsAdmissible (h : ℕ → ℝ) : Prop :=
  (∀ N, Even N → 4 ≤ N → 0 < h N) ∧ EvenTendstoInfinity h ∧
  EvenEventually (fun N => zeroFreeWidth N h ≤ 1 / 4)

def SpectralR (N : ℕ) [NeZero N] (a : ℝ) (ha : a < beta) : Prop :=
  ∀ q : Quaternion ℝ, spectralQuaternion N (residualOperator ha N) q = 0 → q.re = 1 / 2

def SpectralZeroFree (N : ℕ) [NeZero N] (a : ℝ) (ha : a < beta) (η : ℝ) : Prop :=
  ∀ q : Quaternion ℝ, 1 - η < q.re → spectralQuaternion N (residualOperator ha N) q ≠ 0

def HypothesisR : Prop := EvenEventually (fun N => GRH N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta), @SpectralR N _hN (alpha N) ha)

def HypothesisS (h : ℕ → ℝ) : Prop := IsAdmissible h ∧ EvenEventually (fun N => GRH N →
  ∀ (_hN : NeZero N) (ha : alpha N < beta),
    @SpectralZeroFree N _hN (alpha N) ha (zeroFreeWidth N h))

def HypothesisRAt (c : ℝ) : Prop := EvenEventually (fun N => GRH N →
  ∀ (_ : NeZero N) (ha : alpha N c < beta), SpectralR N (alpha N c) ha)

def HypothesisSAt (c : ℝ) (h : ℕ → ℝ) : Prop := IsAdmissible h ∧
  EvenEventually (fun N => GRH N → ∀ (_ : NeZero N) (ha : alpha N c < beta),
    SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h))

end ConditionalGoldbach
