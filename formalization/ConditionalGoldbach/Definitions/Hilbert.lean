module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Hilbert–Schmidt and trace-class operators and diagonal spectral data. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def paperInner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : H) : ℂ := inner ℂ v u

def IsHilbertSchmidt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => ‖T (b j)‖ ^ 2)

def hsNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : ℝ :=
  if h : ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => ‖T (b j)‖ ^ 2)
  then Real.sqrt (∑' j, ‖T ((Classical.choose h) j)‖ ^ 2) else 0

def IsPositiveTraceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  T.IsSymmetric ∧ (∀ x, 0 ≤ (paperInner (T x) x).re) ∧
  ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => (paperInner (T (b j)) (b j)).re)

def positiveTrace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : ℝ :=
  if h : ∃ b : HilbertBasis ℕ ℂ H, Summable (fun j => (paperInner (T (b j)) (b j)).re)
  then ∑' j, (paperInner (T ((Classical.choose h) j)) ((Classical.choose h) j)).re else 0

structure SpectralData {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) where
  basis : HilbertBasis ℕ ℂ H
  values : ℕ → ℝ
  diagonal : ∀ j, T (basis j) = (values j : ℂ) • basis j
  squareSummable : Summable (fun j => values j ^ 2)

def eigenvalues {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : ℕ → ℝ :=
  if h : Nonempty (SpectralData T) then (Classical.choice h).values else 0

def positiveFredholmDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (t : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - t * (eigenvalues A j : ℂ))

def fredholmSquareDet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (t : ℂ) : ℂ :=
  positiveFredholmDet (T.comp T) t

end ConditionalGoldbach
