import LiLiuGoldbach.Proofs.SpectralAlgebra

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertBasis_hasSum_sq_inner (b : HilbertBasis ℕ ℂ H) (x : H) :
    HasSum (fun j => ‖inner ℂ (b j) x‖ ^ 2) (‖x‖ ^ 2) := by
  have hh := Complex.hasSum_re (b.hasSum_inner_mul_inner x x)
  convert hh using 1
  · funext j
    rw [← inner_conj_symm (𝕜 := ℂ) x (b j), mul_comm, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm

/-- The Hilbert--Schmidt square sum of a symmetric operator does not depend on the basis. -/
theorem symmetric_hs_basis_independent (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (b c : HilbertBasis ℕ ℂ H) (hb : Summable (fun j => ‖T (b j)‖ ^ 2)) :
    Summable (fun j => ‖T (c j)‖ ^ 2) ∧
      (∑' j, ‖T (b j)‖ ^ 2) = ∑' j, ‖T (c j)‖ ^ 2 := by
  let f : ℕ → ℕ → ℝ := fun i j => ‖inner ℂ (c j) (T (b i))‖ ^ 2
  have hrow (i : ℕ) : HasSum (f i) (‖T (b i)‖ ^ 2) :=
    hilbertBasis_hasSum_sq_inner c (T (b i))
  have hflip (i j : ℕ) : f i j = ‖inner ℂ (b i) (T (c j))‖ ^ 2 := by
    dsimp [f]
    rw [← hT.apply_clm (c j) (b i), norm_inner_symm]
  have hcol (j : ℕ) : HasSum (fun i => f i j) (‖T (c j)‖ ^ 2) := by
    simpa only [hflip] using hilbertBasis_hasSum_sq_inner b (T (c j))
  have hp : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).2
    refine ⟨fun i => (hrow i).summable, ?_⟩
    convert hb using 1
    funext i
    exact (hrow i).tsum_eq
  have hp' : Summable (fun p : ℕ × ℕ => f p.2 p.1) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.2 hp
  refine ⟨?_, ?_⟩
  · convert hp'.prod using 1
    funext j
    exact (hcol j).tsum_eq.symm
  · calc
      (∑' j, ‖T (b j)‖ ^ 2) = ∑' i, ∑' j, f i j := by simp only [(hrow _).tsum_eq]
      _ = ∑' j, ∑' i, f i j := hp.tsum_comm.symm
      _ = ∑' j, ‖T (c j)‖ ^ 2 := by simp only [(hcol _).tsum_eq]

/-- Squaring a symmetric Hilbert--Schmidt operator gives a positive trace-class operator. -/
theorem symmetric_square_positiveTraceClass (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (hHS : IsHilbertSchmidt T) : IsPositiveTraceClass (T.comp T) := by
  obtain ⟨b, hb⟩ := hHS
  have hquad (x : H) : (paperInner ((T.comp T) x) x).re = ‖T x‖ ^ 2 := by
    change (inner ℂ x (T (T x))).re = _
    rw [← hT.apply_clm x (T x)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (T x)
  refine ⟨?_, fun x => by rw [hquad]; positivity, b, ?_⟩
  · intro x y
    change inner ℂ (T (T x)) y = inner ℂ x (T (T y))
    rw [hT.apply_clm (T x) y, hT.apply_clm x (T y)]
  · simpa only [hquad] using hb

/-- The trace of the square equals the squared Hilbert--Schmidt norm, with both arbitrary
basis choices in the original definitions explicitly discharged. -/
theorem symmetric_square_trace_eq_hsNorm (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (hHS : IsHilbertSchmidt T) : positiveTrace (T.comp T) = hsNorm T ^ 2 := by
  have hquad (x : H) : (paperInner ((T.comp T) x) x).re = ‖T x‖ ^ 2 := by
    change (inner ℂ x (T (T x))).re = _
    rw [← hT.apply_clm x (T x)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (T x)
  have htrace : ∃ b : HilbertBasis ℕ ℂ H,
      Summable (fun j => (paperInner ((T.comp T) (b j)) (b j)).re) :=
    (symmetric_square_positiveTraceClass T hT hHS).2.2
  unfold IsHilbertSchmidt at hHS
  unfold positiveTrace hsNorm
  rw [dite_eq_left htrace, dite_eq_left hHS, Real.sq_sqrt (tsum_nonneg fun j => sq_nonneg _)]
  simp only [hquad]


/-- Real diagonal spectral data imply symmetry of the operator on the whole Hilbert space. -/
theorem SpectralData.isSymmetric {T : H →L[ℂ] H} (d : SpectralData T) : T.IsSymmetric := by
  intro x y
  change inner ℂ (T x) y = inner ℂ x (T y)
  rw [← d.basis.repr.inner_map_map (T x) y, ← d.basis.repr.inner_map_map x (T y),
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  rw [SpectralData.repr_apply d x j, SpectralData.repr_apply d y j]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- Diagonal square summability is the original Hilbert--Schmidt predicate. -/
theorem SpectralData.isHilbertSchmidt {T : H →L[ℂ] H} (d : SpectralData T) : IsHilbertSchmidt T := by
  refine ⟨d.basis, ?_⟩
  have hn (j : ℕ) : ‖T (d.basis j)‖ ^ 2 = d.values j ^ 2 := by
    rw [d.diagonal, norm_smul, d.basis.orthonormal.norm_eq_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [hn] using d.squareSummable

/-- The Hilbert--Schmidt norm is the square sum for any diagonal spectral data. -/
theorem SpectralData.hsNorm_sq {T : H →L[ℂ] H} (d : SpectralData T) :
    hsNorm T ^ 2 = ∑' j, d.values j ^ 2 := by
  have hHS := d.isHilbertSchmidt
  unfold IsHilbertSchmidt at hHS
  unfold hsNorm
  rw [dite_eq_left hHS, Real.sq_sqrt (tsum_nonneg fun j => sq_nonneg _)]
  rw [(symmetric_hs_basis_independent T d.isSymmetric (Classical.choose hHS)
    d.basis (Classical.choose_spec hHS)).2]
  apply tsum_congr
  intro j
  rw [d.diagonal, norm_smul, d.basis.orthonormal.norm_eq_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Squaring spectral data gives spectral data for the squared operator. -/
def SpectralData.square {T : H →L[ℂ] H} (d : SpectralData T) : SpectralData (T.comp T) where
  basis := d.basis
  values := fun j => d.values j ^ 2
  diagonal := by
    intro j
    simp only [ContinuousLinearMap.comp_apply, d.diagonal, map_smul, smul_smul,
      Complex.ofReal_pow, pow_two, Complex.ofReal_mul]
  squareSummable := by
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _
      (d.squareSummable.mul_left (‖T‖ ^ 2))
    intro j
    have hb := (sq_le_sq₀ (abs_nonneg (d.values j)) (norm_nonneg T)).2 (d.abs_value_le_norm j)
    rw [sq_abs] at hb
    nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (d.values j))]

end LiLiuGoldbach16
