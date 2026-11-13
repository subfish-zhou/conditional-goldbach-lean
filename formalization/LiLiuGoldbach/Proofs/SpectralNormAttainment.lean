import LiLiuGoldbach.Proofs.SpectralBasisExistence

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex InnerProductSpace
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A nonzero square-summable diagonal spectrum attains the operator norm. -/
theorem spectral_norm_attained (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T))
    (hne : T ≠ 0) : ∃ j, |eigenvalues T j| = ‖T‖ := by
  have normBound (M : ℝ) (hM : 0 ≤ M) :
      ‖T‖ ≤ M ↔ ∀ j, |eigenvalues T j| ≤ M := by
    simpa only [eigenvalues, dite_eq_left hT] using (Classical.choice hT).norm_le_iff M hM
  have hp : 0 < ‖T‖ := norm_pos_iff.mpr hne
  have hs := finite_large_eigenvalues T hT (‖T‖ / 2) (half_pos hp)
  have hex : ∃ j, ‖T‖ / 2 < |eigenvalues T j| := by
    by_contra! h
    have hn := (normBound _ (by positivity)).mpr h
    linarith
  have hnefin : hs.toFinset.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, hs.mem_toFinset.mpr hj⟩
  obtain ⟨j, hj, hmax⟩ := hs.toFinset.exists_max_image (fun j => |eigenvalues T j|) hnefin
  refine ⟨j, le_antisymm (abs_eigenvalues_le_norm T hT j) ?_⟩
  apply (normBound _ (abs_nonneg _)).mpr
  intro k
  by_cases hk : k ∈ hs.toFinset
  · exact hmax k hk
  · have hk' : |eigenvalues T k| ≤ ‖T‖ / 2 := by
      simpa only [hs.mem_toFinset, Set.mem_ofPred_eq, not_lt] using hk
    exact hk'.trans (le_of_lt (hs.mem_toFinset.mp hj))

/-- The abstract norm assertions used in Proposition 5.3. -/
theorem spectral_norm_spec (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) :
    ‖T‖ = sSup (Set.range (fun j => |eigenvalues T j|)) ∧
      (T ≠ 0 → ∃ j, |eigenvalues T j| = ‖T‖) :=
  ⟨norm_eq_ciSup_abs_eigenvalues T hT, spectral_norm_attained T hT⟩

end LiLiuGoldbach16
