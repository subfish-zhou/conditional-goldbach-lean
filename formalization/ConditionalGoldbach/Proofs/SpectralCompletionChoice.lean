module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import ConditionalGoldbach.Proofs.SpectralCompletionTrace

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Different eigenvalues have zero overlap between any two diagonal Hilbert bases. -/
theorem SpectralData.value_eq_of_inner_ne_zero {T : H →L[ℂ] H}
    (d₁ d₂ : SpectralData T) (i j : ℕ)
    (hne : inner ℂ (d₂.basis j) (d₁.basis i) ≠ 0) : d₁.values i = d₂.values j := by
  have hh := d₂.repr_apply (d₁.basis i) j
  simp only [d₂.basis.repr_apply_apply] at hh
  rw [d₁.diagonal, inner_smul_right] at hh
  exact_mod_cast mul_right_cancel₀ hne hh

/-- Every diagonal value occurs in every diagonal Hilbert basis. -/
theorem SpectralData.exists_value_eq {T : H →L[ℂ] H}
    (d₁ d₂ : SpectralData T) (i : ℕ) : ∃ j, d₂.values j = d₁.values i := by
  have hex : ∃ j, inner ℂ (d₂.basis j) (d₁.basis i) ≠ 0 := by
    by_contra! hn
    have hh := (hilbertBasis_hasSum_sq_inner d₂.basis (d₁.basis i)).tsum_eq
    simp only [hn, norm_zero, zero_pow (by decide : 2 ≠ 0), tsum_zero,
      d₁.basis.orthonormal.norm_eq_one, one_pow] at hh
    norm_num at hh
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, (d₁.value_eq_of_inner_ne_zero d₂ i j hj).symm⟩

set_option maxHeartbeats 600000 in
/-- Absolutely summable spectral statistics are independent of the diagonal basis.
The proof uses Parseval twice; it does not posit a permutation of infinite eigenvalue lists. -/
theorem SpectralData.spectralStatistic_independent {T : H →L[ℂ] H}
    (d₁ d₂ : SpectralData T) (F : ℝ → ℂ) (hF : Summable (fun i => F (d₁.values i))) :
    Summable (fun j => F (d₂.values j)) ∧
      (∑' i, F (d₁.values i)) = ∑' j, F (d₂.values j) := by
  let w : ℕ → ℕ → ℝ := fun i j => ‖inner ℂ (d₂.basis j) (d₁.basis i)‖ ^ 2
  have hw (i j : ℕ) : 0 ≤ w i j := sq_nonneg _
  have hrow (i : ℕ) : HasSum (w i) 1 := by
    simpa only [w, d₁.basis.orthonormal.norm_eq_one, one_pow] using
      hilbertBasis_hasSum_sq_inner d₂.basis (d₁.basis i)
  have hcol (j : ℕ) : HasSum (fun i => w i j) 1 := by
    simpa only [w, norm_inner_symm (d₂.basis j), d₂.basis.orthonormal.norm_eq_one, one_pow] using
      hilbertBasis_hasSum_sq_inner d₁.basis (d₂.basis j)
  have hsame (i j : ℕ) : F (d₁.values i) * (w i j : ℂ) = F (d₂.values j) * (w i j : ℂ) := by
    by_cases hzero : inner ℂ (d₂.basis j) (d₁.basis i) = 0
    · simp only [w, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero, mul_zero]
    · rw [d₁.value_eq_of_inner_ne_zero d₂ i j hzero]
  have hn : Summable (fun p : ℕ × ℕ => ‖F (d₁.values p.1)‖ * w p.1 p.2) := by
    apply (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖F (d₁.values p.1)‖ * w p.1 p.2)
      (fun p => mul_nonneg (norm_nonneg _) (hw p.1 p.2))).2
    refine ⟨fun i => ?_, ?_⟩
    · change Summable (fun j => ‖F (d₁.values i)‖ * w i j)
      exact (hrow i).summable.mul_left ‖F (d₁.values i)‖
    · change Summable (fun i => ∑' j, ‖F (d₁.values i)‖ * w i j)
      simpa only [tsum_mul_left, (hrow _).tsum_eq, mul_one] using hF.norm
  let a : ℕ → ℕ → ℂ := fun i j => F (d₁.values i) * (w i j : ℂ)
  have ha : Summable (Function.uncurry a) := by
    apply hn.of_norm_bounded
    intro p
    simp only [Function.uncurry, a, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw p.1 p.2), le_refl]
  have harow (i : ℕ) : (∑' j, a i j) = F (d₁.values i) := by
    simp only [a, tsum_mul_left, ← Complex.ofReal_tsum, (hrow _).tsum_eq,
      Complex.ofReal_one, mul_one]
  have hacol (j : ℕ) : (∑' i, a i j) = F (d₂.values j) := by
    simp only [a, hsame, tsum_mul_left, ← Complex.ofReal_tsum, (hcol _).tsum_eq,
      Complex.ofReal_one, mul_one]
  have ha' : Summable (fun p : ℕ × ℕ => a p.2 p.1) :=
    ((Equiv.prodComm ℕ ℕ).summable_iff (f := Function.uncurry a)).2 ha
  refine ⟨?_, ?_⟩
  · convert ha'.prod using 1
    funext j
    exact (hacol j).symm
  · calc
      (∑' i, F (d₁.values i)) = ∑' i, ∑' j, a i j := by simp only [harow]
      _ = ∑' j, ∑' i, a i j := ha.tsum_comm.symm
      _ = ∑' j, F (d₂.values j) := by simp only [hacol]

/-- Convergent products of scalar spectral statistics are independent of the basis,
including the case where a factor vanishes. -/
theorem SpectralData.tprod_one_add_independent {T : H →L[ℂ] H}
    (d₁ d₂ : SpectralData T) (F : ℝ → ℂ) (hF₁ : Summable (fun i => F (d₁.values i)))
    (hF₂ : Summable (fun j => F (d₂.values j))) :
    (∏' i, (1 + F (d₁.values i))) = ∏' j, (1 + F (d₂.values j)) := by
  by_cases hz : ∃ i, 1 + F (d₁.values i) = 0
  · obtain ⟨i, hi⟩ := hz
    obtain ⟨j, hj⟩ := d₁.exists_value_eq d₂ i
    rw [(hasProd_zero_of_exists_eq_zero ⟨i, hi⟩).tprod_eq,
      (hasProd_zero_of_exists_eq_zero ⟨j, by simpa only [hj] using hi⟩).tprod_eq]
  · have hne₁ : ∀ i, 1 + F (d₁.values i) ≠ 0 := by simpa only [not_exists] using hz
    have hne₂ : ∀ j, 1 + F (d₂.values j) ≠ 0 := by
      intro j
      obtain ⟨i, hi⟩ := d₂.exists_value_eq d₁ j
      simpa only [hi] using hne₁ i
    rw [← Complex.cexp_tsum_eq_tprod hne₁ (Complex.summable_log_one_add_of_summable hF₁),
      ← Complex.cexp_tsum_eq_tprod hne₂ (Complex.summable_log_one_add_of_summable hF₂)]
    congr 1
    exact (d₁.spectralStatistic_independent d₂ (fun x => Complex.log (1 + F x))
      (Complex.summable_log_one_add_of_summable hF₁)).2

theorem proposition_6_1_spectral_choice_independent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (d₁ d₂ : SpectralData T) (t : ℂ) :
    (∏' j : ℕ, (1 - t * (d₁.values j : ℂ) ^ 2)) =
      ∏' j : ℕ, (1 - t * (d₂.values j : ℂ) ^ 2) := by
  have hs (d : SpectralData T) : Summable (fun j => -(t * (d.values j : ℂ) ^ 2)) := by
    have hh := (Complex.summable_ofReal.2 d.squareSummable).mul_left t
    simpa only [Complex.ofReal_pow] using hh.neg
  simpa only [sub_eq_add_neg] using
    d₁.tprod_one_add_independent d₂ (fun x => -(t * (x : ℂ) ^ 2)) (hs d₁) (hs d₂)

end ConditionalGoldbach
