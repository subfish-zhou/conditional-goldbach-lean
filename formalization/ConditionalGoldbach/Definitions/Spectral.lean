module

public import ConditionalGoldbach.Definitions.Arithmetic
public import ConditionalGoldbach.Definitions.Hardy
public import ConditionalGoldbach.Definitions.Hilbert
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Quaternion

/-! Spectral definitions used by the conditional Goldbach formalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def spectralScale (N : ℕ) : ℝ :=
  Real.sqrt (singularSeries N / N) * Real.rpow (Real.log N) (3 / 2)

def spectralComplex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (q : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))

def spectralPartialQuaternion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (q : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun z j =>
    z * (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) • (q * (1 - q)))) 1

def spectralQuaternion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (T : H →L[ℂ] H) (q : Quaternion ℝ) : Quaternion ℝ :=
  if h : ∃ y, Tendsto (spectralPartialQuaternion N T q) atTop (𝓝 y)
  then Classical.choose h else 0

def IntrinsicEntire (F : Quaternion ℝ → Quaternion ℝ) : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ z, f (conj z) = conj (f z)) ∧
    ∀ J : Quaternion ℝ, J.re = 0 → J ^ 2 = -1 → ∀ z : ℂ,
      F ((z.re : Quaternion ℝ) + z.im • J) = (f z).re + (f z).im • J

def spectralWidthFromBound (N : ℕ) (M : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - spectralScale N ^ 2 / M ^ 2)) / 2

def spectralRootParameter (N : ℕ) (μ : ℝ) : ℝ :=
  spectralScale N ^ 2 / μ ^ 2

def quaternionSlice (J : Quaternion ℝ) : Set (Quaternion ℝ) :=
  {q | ∃ x y : ℝ, q = (x : Quaternion ℝ) + y • J}

def complexQuaternion (z : ℂ) : Quaternion ℝ := ⟨z.re, z.im, 0, 0⟩

def fueterOperator (F : ℂ → ℂ → ℂ) (s z : ℂ) : Quaternion ℝ :=
  complexQuaternion (wirtingerBar (fun u => F u z) s) +
    (⟨0, 0, 1, 0⟩ : Quaternion ℝ) * complexQuaternion (wirtinger (F s) z)

def spectralPartialQuaternionReindexed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (N : ℕ) (T : H →L[ℂ] H)
    (e : ℕ ≃ ℕ) (q : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun acc j =>
    acc * (1 - (4 * eigenvalues T (e j) ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q))) 1

def centeredSpectralPartial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (N : ℕ) (T : H →L[ℂ] H)
    (ξ : Quaternion ℝ) (k : ℕ) : Quaternion ℝ :=
  (List.range k).foldl (fun acc j => acc *
    (1 - (eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) +
      (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * ξ ^ 2)) 1

end ConditionalGoldbach
