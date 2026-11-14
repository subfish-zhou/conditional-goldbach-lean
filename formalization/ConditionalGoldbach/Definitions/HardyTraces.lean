module

public import ConditionalGoldbach.Proofs.HardyBoundary

/-! Interior restrictions and endpoint traces of Hardy functions. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

theorem interiorLine_memLp {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Ioo a b) (ψ : HardySpace a b) :
    MemLp (fun t : ℝ => fourierLaplace ψ (line x t)) 2 volume := by
  exact hardy_interiorLine_memLp hab hx ψ

def interiorLine {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (x : ℝ) (hx : x ∈ Ioo a b) : Lp ℂ 2 (volume : Measure ℝ) :=
  (interiorLine_memLp hab hx ψ).toLp _

def IsBoundaryTrace {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (left right : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  Tendsto (fun x : Ioo a b => interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin a (Ioo a b))) (𝓝 left) ∧
  Tendsto (fun x : Ioo a b => interiorLine hab ψ x x.property)
    (comap Subtype.val (nhdsWithin b (Ioo a b))) (𝓝 right)

theorem boundaryTraces_exist {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    ∃ p : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ),
      IsBoundaryTrace hab ψ p.1 p.2 := by
  simpa only [IsBoundaryTrace, interiorLine] using hardy_boundaryTraces_exist hab ψ

def boundaryTraces {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :=
  Classical.choose (boundaryTraces_exist hab ψ)

end ConditionalGoldbach
