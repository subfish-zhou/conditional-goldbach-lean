import ConditionalGoldbach.Proofs.ModelContinuation
import ConditionalGoldbach.Proofs.CharacterAnalytic

/-! Joint holomorphy and exact conjugation symmetries of the residual kernel. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

lemma conj_nonnegReal_cpow (x : ℝ) (hx : 0 ≤ x) (s : ℂ) :
    conj ((x : ℂ)^s) = (x : ℂ)^(conj s) := by
  simpa using (Complex.conj_cpow (x : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hx]; exact ne_of_lt Real.pi_pos)).symm

lemma conj_tprod_complex {ι : Type*} (f : ι → ℂ) :
    conj (∏' i, f i) = ∏' i, conj (f i) := by
  exact Function.LeftInverse.map_tprod (g := starRingEnd ℂ) f
    continuous_star continuous_star (fun z => star_star z)

lemma densityEulerProduct_conj (N : ℕ) (w : ℂ) :
    conj (densityEulerProduct N w) = densityEulerProduct N (conj w) := by
  unfold densityEulerProduct
  rw [conj_tprod_complex]
  apply tprod_congr
  intro p
  split_ifs <;> simp [map_add, map_div₀, map_sub, conj_natCast_cpow, map_ofNat]

lemma gammaQuotient_conj (s : ℂ) : conj (gammaQuotient s) = gammaQuotient (conj s) := by
  unfold gammaQuotient
  rw [map_div₀, ← Complex.Gamma_conj, ← Complex.Gamma_conj]
  congr 1 <;> congr 1 <;> simp [map_ofNat]

lemma continuedModel_symmetric (N : ℕ) (s z : ℂ) :
    continuedModel N s z = continuedModel N z s := by
  unfold continuedModel
  rw [add_comm z s, show (1 : ℂ)-z-s = 1-s-z by ring]
  ring

lemma continuedModel_conj (N : ℕ) (s z : ℂ) :
    conj (continuedModel N s z) = continuedModel N (conj s) (conj z) := by
  unfold continuedModel
  simp only [map_mul, densityEulerProduct_conj, gammaQuotient_conj,
    ← riemannZeta_conj, map_sub, map_add, map_one, Complex.conj_ofReal]
  have hc : conj (((Real.pi : ℂ) / N)^(s+z)) =
      ((Real.pi : ℂ)/N)^(conj s+conj z) := by
    simpa using conj_nonnegReal_cpow (Real.pi / N) (by positivity) (s+z)
  rw [hc]

lemma diagonalSeries_conj (N : ℕ) (w : ℂ) :
    conj (diagonalSeries N w) = diagonalSeries N (conj w) := by
  unfold diagonalSeries
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  split_ifs <;> simp [map_div₀, map_pow, conj_natCast_cpow]

lemma residual_symmetric (N : ℕ) [NeZero N] (s z : ℂ) : residual N s z = residual N z s := by
  unfold residual
  rw [characterKernel_symmetric, continuedModel_symmetric, add_comm s z]

lemma residual_conj (N : ℕ) [NeZero N] (s z : ℂ) :
    conj (residual N s z) = residual N (conj s) (conj z) := by
  simp only [residual, map_sub, characterKernel_conjugation, diagonalSeries_conj,
    continuedModel_conj, map_add]

lemma residual_hermitian (N : ℕ) [NeZero N] :
    HermitianKernel (fun s z => residual N s (conj z)) := by
  intro s z
  rw [residual_conj, Complex.conj_conj, residual_symmetric]

lemma residual_differentiableOn (N : ℕ) [NeZero N] (hN : 0 < N) (hGRH : GRH N) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => residual N p.1 p.2) analyticDomain := by
  have hK := (characterKernel_differentiableOn_of_GRH hGRH).mono
    (show analyticDomain ⊆ {p : ℂ × ℂ | 0 < p.1.re ∧ 0 < p.2.re} from
      fun p hp => ⟨hp.1, hp.2.2.1⟩)
  have hD : DifferentiableOn ℂ (fun p : ℂ × ℂ => diagonalSeries N (p.1+p.2)) analyticDomain := by
    intro p hp
    have hs : 0 < (p.1+p.2).re := by simpa only [add_re] using add_pos hp.1 hp.2.2.1
    exact (DifferentiableAt.comp (g := diagonalSeries N)
      (f := fun q : ℂ × ℂ => q.1+q.2) p (diagonalSeries_differentiableAt N hs) (by fun_prop)).differentiableWithinAt
  exact (hK.sub hD).sub (continuedModel_differentiableOn N hN)

theorem proposition_4_5 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) (hGRH : GRH N) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => residual N p.1 p.2) analyticDomain ∧
    (∀ s z : ℂ, residual N s z = residual N z s ∧
      conj (residual N s z) = residual N (conj s) (conj z)) ∧
    HermitianKernel (fun s z => residual N s (conj z)) := by
  exact ⟨residual_differentiableOn N (by omega) hGRH,
    fun s z => ⟨residual_symmetric N s z, residual_conj N s z⟩, residual_hermitian N⟩

end ConditionalGoldbach
