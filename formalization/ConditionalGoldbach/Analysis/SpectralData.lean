module

public import ConditionalGoldbach.Definitions.Hilbert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Coordinate and norm identities for diagonal spectral data on a Hilbert space. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter Set Complex
namespace ConditionalGoldbach
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The selected spectral data really give a square-summable eigenvalue family. -/
theorem eigenvalues_square_summable (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) :
    Summable (fun j => eigenvalues T j ^ 2) := by
  simp only [eigenvalues, dite_eq_left hT]
  exact (Classical.choice hT).squareSummable

/-- Each real diagonal value is bounded in absolute value by the operator norm. -/
theorem SpectralData.abs_value_le_norm {T : H →L[ℂ] H} (d : SpectralData T) (j : ℕ) :
    |d.values j| ≤ ‖T‖ := by
  have hb : ‖d.basis j‖ = 1 := d.basis.orthonormal.norm_eq_one j
  have h := T.le_opNorm (d.basis j)
  rw [d.diagonal j, norm_smul, Complex.norm_real, Real.norm_eq_abs, hb, mul_one, mul_one] at h
  exact h

theorem abs_eigenvalues_le_norm (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) (j : ℕ) :
    |eigenvalues T j| ≤ ‖T‖ := by
  simp only [eigenvalues, dite_eq_left hT]
  exact (Classical.choice hT).abs_value_le_norm j

/-- Diagonal action on all Hilbert coordinates, obtained by mapping the basis expansion. -/
theorem SpectralData.repr_apply {T : H →L[ℂ] H} (d : SpectralData T) (x : H) (j : ℕ) :
    d.basis.repr (T x) j = (d.values j : ℂ) * d.basis.repr x j := by
  have h := (d.basis.hasSum_repr x).mapL ((innerSL ℂ (d.basis j)).comp T)
  have hb := orthonormal_iff_ite.mp d.basis.orthonormal
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul,
    d.diagonal, hb] at h
  have hh := h.tsum_eq
  simp only [smul_eq_mul, mul_ite, mul_zero, tsum_ite_eq', mul_one] at hh
  rw [d.basis.repr_apply_apply, ← hh]
  ring
/-- A uniform bound on the real diagonal values bounds the full operator norm. -/
theorem SpectralData.norm_le {T : H →L[ℂ] H} (d : SpectralData T) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |d.values j| ≤ M) : ‖T‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  have h : ‖d.basis.repr (T x)‖ ≤ ‖(M : ℂ) • d.basis.repr x‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro j
    rw [SpectralData.repr_apply d x j]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, lp.coeFn_smul, Pi.smul_apply,
      norm_smul, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hbound j) (norm_nonneg _)
  simpa only [LinearIsometryEquiv.norm_map, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hM] using h
/-- Full norm equality; the bound is over the whole Hilbert basis, including the kernel. -/
theorem SpectralData.norm_eq_ciSup_abs_values {T : H →L[ℂ] H} (d : SpectralData T) : ‖T‖ = ⨆ j, |d.values j| := by
  have hb : BddAbove (Set.range fun j => |d.values j|) := by
    refine ⟨‖T‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact d.abs_value_le_norm j
  have hnonneg : 0 ≤ ⨆ j, |d.values j| :=
    le_trans (abs_nonneg (d.values 0)) (le_ciSup hb 0)
  apply le_antisymm
  · exact SpectralData.norm_le d _ hnonneg (fun j => le_ciSup hb j)
  · exact ciSup_le (fun j => d.abs_value_le_norm j)
/-- Square summability leaves only finitely many eigenvalues above a positive threshold. -/
theorem finite_large_eigenvalues (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T))
    (δ : ℝ) (hδ : 0 < δ) : Set.Finite {j | δ < |eigenvalues T j|} := by
  have hevent : ∀ᶠ j in cofinite, eigenvalues T j ^ 2 < δ ^ 2 :=
    (eigenvalues_square_summable T hT).tendsto_cofinite_zero.eventually
      (gt_mem_nhds (sq_pos_of_pos hδ))
  have hfinite : Set.Finite {j | δ ^ 2 ≤ eigenvalues T j ^ 2} := by
    simpa only [Filter.eventually_cofinite, not_lt] using hevent
  apply hfinite.subset
  intro j hj
  change δ < |eigenvalues T j| at hj
  change δ ^ 2 ≤ eigenvalues T j ^ 2
  nlinarith [sq_abs (eigenvalues T j)]

/-- The norm bound is equivalent to the pointwise spectral bound. -/
theorem SpectralData.norm_le_iff {T : H →L[ℂ] H} (d : SpectralData T)
    (M : ℝ) (hM : 0 ≤ M) : ‖T‖ ≤ M ↔ ∀ j, |d.values j| ≤ M := by
  constructor
  · intro h j
    exact (d.abs_value_le_norm j).trans h
  · exact d.norm_le M hM

/-- The canonical eigenvalue choice has the same supremum as the operator norm. -/
theorem norm_eq_ciSup_abs_eigenvalues (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) :
    ‖T‖ = ⨆ j, |eigenvalues T j| := by
  simp only [eigenvalues, dite_eq_left hT]
  exact (Classical.choice hT).norm_eq_ciSup_abs_values


end ConditionalGoldbach
