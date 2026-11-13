import LiLiuGoldbach.Proofs.KernelRegularity
import LiLiuGoldbach.Proofs.SpectralDictionary
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Matrix Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

lemma finiteSpectralMatrix_isHermitian : finiteSpectralMatrix.IsHermitian := by
  ext i j
  change conj (finiteSpectralMatrix j i) = finiteSpectralMatrix i j
  simp only [finiteSpectralMatrix,map_mul,Complex.conj_ofReal]
  rw [weightedKernel_hermitian experimentN]
  simp only [Complex.conj_conj]
  ring

lemma finiteEigenvalues_spec : IsFiniteSpectrum finiteEigenvalues := by
  have h := finiteSpectralMatrix_isHermitian
  have hex : ∃ ev, IsFiniteSpectrum ev := by
    refine ⟨h.eigenvalues,h.eigenvectorUnitary,Unitary.coe_star_mul_self _,Unitary.coe_mul_star_self _,?_⟩
    simpa only [Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_eq_complex_ofReal] using h.spectral_theorem
  simpa only [finiteEigenvalues, dite_eq_left hex] using Classical.choose_spec hex

lemma unitary_column_norm {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : star U * U = 1) (j : n) :
    ‖(WithLp.toLp 2 (fun i => U i j) : EuclideanSpace ℂ n)‖ = 1 := by
  have hh := congrArg (fun A : Matrix n n ℂ => (A j j).re) hU
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply_eq,star_def,Complex.mul_re,Complex.one_re,
    Complex.conj_re,Complex.conj_im] at hh
  change Complex.reCLM (∑ k, conj (U k j)*U k j)=1 at hh
  rw [map_sum] at hh
  simp only [Complex.reCLM_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im] at hh
  have hs : ‖(WithLp.toLp 2 (fun i => U i j) : EuclideanSpace ℂ n)‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖U i j‖^2)=1
    simpa only [Complex.sq_norm,Complex.normSq_apply,neg_mul,sub_neg_eq_add] using hh
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => U i j) : EuclideanSpace ℂ n)]

lemma unitary_column_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ) (ev : n → ℝ) (hU : star U * U = 1)
    (hA : A = U * Matrix.diagonal (fun i => (ev i : ℂ)) * star U) (j : n) :
    A.mulVec (fun i => U i j) = (ev j : ℂ) • (fun i => U i j) := by
  have hh : A*U = U*Matrix.diagonal (fun i => (ev i : ℂ)) := by
    rw [hA]
    simp only [mul_assoc,hU,mul_one]
  ext i
  have hi := congrArg (fun M : Matrix n n ℂ => M i j) hh
  simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.diagonal_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hi

lemma finiteEigenvalue_le_norm (j : Fin 2562) : |finiteEigenvalues j| ≤ finiteMatrixOpNorm := by
  obtain ⟨U,hU,hU',hA⟩ := finiteEigenvalues_spec
  let T : EuclideanSpace ℂ (Fin 2562) →L[ℂ] EuclideanSpace ℂ (Fin 2562) :=
    finiteSpectralMatrix.toEuclideanLin.toContinuousLinearMap
  have hT (x : EuclideanSpace ℂ (Fin 2562)) : T x = WithLp.toLp 2 (finiteSpectralMatrix.mulVec (WithLp.ofLp x)) := rfl
  have hb : BddAbove {r : ℝ | ∃ x : EuclideanSpace ℂ (Fin 2562), ‖x‖=1 ∧
      r=‖(WithLp.toLp 2 (finiteSpectralMatrix.mulVec (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin 2562))‖} := by
    refine ⟨‖T‖,?_⟩
    rintro r ⟨x,hx,rfl⟩
    rw [← hT]
    simpa [hx] using T.le_opNorm x
  apply le_csSup hb
  let x : EuclideanSpace ℂ (Fin 2562) := WithLp.toLp 2 (fun i => U i j)
  refine ⟨x,unitary_column_norm U hU j,?_⟩
  have he := unitary_column_eigenvector finiteSpectralMatrix U finiteEigenvalues hU hA j
  change |finiteEigenvalues j| = ‖(WithLp.toLp 2 (finiteSpectralMatrix.mulVec (fun i => U i j)) : EuclideanSpace ℂ (Fin 2562))‖
  rw [he]
  change |finiteEigenvalues j| = ‖(finiteEigenvalues j : ℂ) • x‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,unitary_column_norm U hU j,mul_one]


lemma finiteSpectralFunction_product (q : ℂ) :
    finiteSpectralFunction q = ∏ j : Fin 2562,
      (1-(4*finiteEigenvalues j^2/spectralScale experimentN^2 : ℝ)*q*(1-q)) := by
  obtain ⟨U,hU,hU',hA⟩ := finiteEigenvalues_spec
  let D := Matrix.diagonal (fun i => (finiteEigenvalues i : ℂ))
  let k := 4*q*(1-q)/(spectralScale experimentN : ℂ)^2
  have hAA : finiteSpectralMatrix*finiteSpectralMatrix = U*(D*D)*star U := by
    rw [hA]
    change (U*D*star U)*(U*D*star U)=_
    calc
      _ = U*D*(star U*U)*D*star U := by noncomm_ring
      _ = _ := by rw [hU]; noncomm_ring
  have he : 1-k • (finiteSpectralMatrix*finiteSpectralMatrix) = U*(1-k • (D*D))*star U := by
    rw [hAA]
    simp only [mul_sub,sub_mul,mul_one,hU',Matrix.mul_smul,Matrix.smul_mul]
  have hdet : Matrix.det U*Matrix.det (star U)=1 := by rw [← Matrix.det_mul,hU',Matrix.det_one]
  change Matrix.det (1-k • (finiteSpectralMatrix*finiteSpectralMatrix))=_
  rw [he,Matrix.det_mul,Matrix.det_mul]
  have hdiag : 1-k • (D*D) = Matrix.diagonal (fun i => 1-k*(finiteEigenvalues i : ℂ)^2) := by
    ext i j
    simp [D,Matrix.mul_diagonal,Matrix.diagonal_apply,Matrix.one_apply,smul_eq_mul]
    split_ifs <;> simp_all [pow_two]
  rw [hdiag,Matrix.det_diagonal]
  calc
    _ = (∏ i, (1-k*(finiteEigenvalues i : ℂ)^2))*(Matrix.det U*Matrix.det (star U)) := by ring
    _ = ∏ i, (1-k*(finiteEigenvalues i : ℂ)^2) := by rw [hdet,mul_one]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      dsimp [k]
      push_cast
      ring

lemma finiteSpectralFunction_reflection (q : ℂ) : finiteSpectralFunction (1-q)=finiteSpectralFunction q := by
  simp only [finiteSpectralFunction_product,sub_sub_cancel]
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma finiteSpectralFunction_zero_critical (hb : finiteMatrixOpNorm ≤ spectralScale experimentN)
    (q : ℂ) (hz : finiteSpectralFunction q=0) : q.re=1/2 := by
  have hδ : 0 < spectralScale experimentN := spectralScale_pos experimentN (by norm_num [experimentN])
    (singularSeries_pos experimentN) (Real.log_pos (by norm_num [experimentN]))
  rw [finiteSpectralFunction_product] at hz
  obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp hz
  obtain ⟨hμ,hroot⟩ := (complex_quadratic_factor_zero_iff _ _ hδ.ne' q).mp hj
  have hμb := (finiteEigenvalue_le_norm j).trans hb
  have hs : finiteEigenvalues j^2 ≤ spectralScale experimentN^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (finiteEigenvalues j)) hμb 2
  have hc : (1:ℝ)/4 ≤ spectralScale experimentN^2/(4*finiteEigenvalues j^2) := by
    apply (le_div_iff₀ (by positivity : 0<4*finiteEigenvalues j^2)).2
    nlinarith
  by_contra hn
  have hi := congrArg Complex.im hroot
  simp only [Complex.mul_im,Complex.sub_im,Complex.one_im,Complex.sub_re,Complex.one_re,
    Complex.ofReal_im,zero_sub] at hi
  have hi0 : q.im=0 := by
    have hh : (1-2*q.re)*q.im=0 := by nlinarith
    exact (mul_eq_zero.mp hh).resolve_left (by intro h; apply hn; linarith)
  have hr := congrArg Complex.re hroot
  simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,
    Complex.ofReal_re,hi0,mul_zero,sub_zero] at hr
  have hh : (q.re-1/2)^2=0 := by nlinarith [sq_nonneg (q.re-1/2)]
  exact hn (by nlinarith [sq_eq_zero_iff.mp hh])

theorem proposition_B_5 (hGRH : GRH experimentN) :
    IsFiniteSpectrum finiteEigenvalues ∧
    (∀ q : ℂ, finiteSpectralFunction q =
      ∏ j : Fin 2562, (1 - (4 * finiteEigenvalues j ^ 2 / spectralScale experimentN ^ 2 : ℝ) * q * (1 - q))) ∧
    (∀ q : ℂ, finiteSpectralFunction (1 - q) = finiteSpectralFunction q) ∧
    (finiteMatrixOpNorm ≤ spectralScale experimentN →
      ∀ q : ℂ, finiteSpectralFunction q = 0 → q.re = 1 / 2)  := by
  exact ⟨finiteEigenvalues_spec,finiteSpectralFunction_product,finiteSpectralFunction_reflection,
    finiteSpectralFunction_zero_critical⟩

end LiLiuGoldbach16
