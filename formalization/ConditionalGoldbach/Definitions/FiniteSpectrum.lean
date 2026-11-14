module

public import ConditionalGoldbach.Definitions.Experiment
public import ConditionalGoldbach.Definitions.Operators
public import ConditionalGoldbach.Definitions.Spectral
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! FiniteSpectrum definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def spectralNode (i : Fin 2562) : ℂ :=
  line (if i.val < 1281 then alpha experimentN else beta) (((i.val % 1281 : ℕ) : ℝ) / 16 - 40)

def trapezoidWeight (i : Fin 2562) : ℝ :=
  (1 / 16) * if i.val % 1281 = 0 ∨ i.val % 1281 = 1280 then 1 / 2 else 1

def finiteSpectralMatrix : Matrix (Fin 2562) (Fin 2562) ℂ :=
  fun i j => (Real.sqrt (trapezoidWeight i) : ℂ) *
    weightedKernel experimentN (spectralNode i) (spectralNode j) * Real.sqrt (trapezoidWeight j)

def finiteSpectralFunction (q : ℂ) : ℂ :=
  Matrix.det (1 - (4 * q * (1 - q) / spectralScale experimentN ^ 2) •
    (finiteSpectralMatrix * finiteSpectralMatrix))

def IsFiniteSpectrum (ev : Fin 2562 → ℝ) : Prop :=
  ∃ U : Matrix (Fin 2562) (Fin 2562) ℂ,
    star U * U = 1 ∧ U * star U = 1 ∧
    finiteSpectralMatrix = U * Matrix.diagonal (fun i => (ev i : ℂ)) * star U

def finiteEigenvalues : Fin 2562 → ℝ :=
  if h : ∃ ev, IsFiniteSpectrum ev then Classical.choose h else 0

def finiteMatrixOpNorm : ℝ :=
  sSup {r : ℝ | ∃ x : EuclideanSpace ℂ (Fin 2562), ‖x‖ = 1 ∧
    r = ‖(WithLp.toLp 2 (finiteSpectralMatrix.mulVec (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin 2562))‖}

end ConditionalGoldbach
