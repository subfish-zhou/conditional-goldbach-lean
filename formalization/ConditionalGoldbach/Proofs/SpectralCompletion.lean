import ConditionalGoldbach.Proofs.SpectralConsequences

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every real algebra embedding of the complex numbers into quaternions respects conjugation. -/
theorem quaternion_algHom_map_conj (f : ℂ →ₐ[ℝ] Quaternion ℝ) (z : ℂ) :
    f (conj z) = star (f z) := by
  have hs : (f I) ^ 2 = -1 := by rw [← map_pow]; simp
  have hn : Quaternion.normSq (f I) = 1 := by
    have hh := congrArg Quaternion.normSq hs
    simp only [map_pow, Quaternion.normSq_neg, map_one] at hh
    nlinarith [(Quaternion.normSq_nonneg : 0 ≤ Quaternion.normSq (f I))]
  have hr : (f I).re = 0 := (Quaternion.sq_eq_neg_normSq (a := f I)).mp (by simpa [hn] using hs)
  have hstar : star (f I) = -f I := (Quaternion.star_eq_neg).mpr hr
  have hsplit (w : ℂ) : f w = (w.re : Quaternion ℝ) + w.im • f I := by
    nth_rw 1 [← Complex.re_add_im w]
    have hreal (x : ℝ) : f (x : ℂ) = (x : Quaternion ℝ) := f.commutes x
    simp only [map_add, map_mul, hreal]
    rw [Quaternion.coe_mul_eq_smul]
  rw [hsplit (conj z), hsplit z]
  simp [Quaternion.star_smul, hstar]

/-- Complex conjugation commutes with the scalar spectral product. -/
theorem spectralComplex_conj (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : ℂ) :
    spectralComplex N T (conj q) = conj (spectralComplex N T q) := by
  have hm := (spectralComplex_multipliable N T hT q).map_tprod
    (starRingEnd ℂ).toMonoidHom Complex.continuous_conj
  change conj (spectralComplex N T q) = ∏' j : ℕ, conj (1 -
    (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q)) at hm
  simpa only [spectralComplex, map_sub, map_mul, map_one, conj_ofReal] using hm.symm

/-- Quaternionic conjugation symmetry holds on every complex slice. -/
theorem spectralQuaternion_star (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (q : Quaternion ℝ) :
    spectralQuaternion N T (star q) = star (spectralQuaternion N T q) := by
  obtain ⟨f, z, rfl⟩ := quaternion_exists_complex_slice q
  rw [← quaternion_algHom_map_conj, spectralQuaternion_apply_algHom N T hT,
    spectralComplex_conj N T hT, quaternion_algHom_map_conj,
    spectralQuaternion_apply_algHom N T hT]

/-- Outside the open unit interval the real product has every factor at least one. -/
theorem spectralQuaternion_real_ge_one (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (x : ℝ) (hx : x ∉ Ioo 0 1) :
    1 ≤ (spectralQuaternion N T x).re := by
  have hprod : x * (1 - x) ≤ 0 := by
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with hx | hx
    · exact mul_nonpos_of_nonpos_of_nonneg hx (by linarith)
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hfactor (j : ℕ) : 1 ≤ 1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2) * x * (1 - x) := by
    have hc : 0 ≤ 4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 := by positivity
    have := mul_nonpos_of_nonneg_of_nonpos hc hprod
    nlinarith
  have hseq (k : ℕ) :
      spectralPartialQuaternion N T x k =
        ((∏ j ∈ Finset.range k, (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2) * x * (1 - x)) : ℝ) : Quaternion ℝ) := by
    induction k with
    | zero => simp [spectralPartialQuaternion]
    | succ k ih =>
      have hrec : spectralPartialQuaternion N T x (k + 1) = spectralPartialQuaternion N T x k *
          (1 - (4 * eigenvalues T k ^ 2 / spectralScale N ^ 2 : ℝ) • ((x : Quaternion ℝ) * (1 - x))) := by
        simp [spectralPartialQuaternion, List.range_succ, List.foldl_append]
      rw [hrec, ih, Finset.prod_range_succ]
      simp only [← Quaternion.coe_one, ← Quaternion.coe_sub, ← Quaternion.coe_mul,
        Quaternion.smul_coe, smul_eq_mul, mul_assoc]
  have ht := Quaternion.continuous_re.continuousAt.tendsto.comp
    (spectralPartialQuaternion_tendsto N T hT x)
  apply ge_of_tendsto' ht
  intro k
  change 1 ≤ (spectralPartialQuaternion N T x k).re
  rw [hseq, Quaternion.re_coe]
  exact Finset.one_le_prod₀ fun j _ => hfactor j

theorem proposition_6_2 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    let X := spectralQuaternion N (residualOperator ha N)
    X 0 = 1 ∧ X 1 = 1 ∧ (∀ q, X (1 - q) = X q) ∧
    (∀ q, X (star q) = star (X q)) ∧ (∀ q, X (1 - star q) = star (X q)) ∧
    (∀ ξ, X (1 / 2 + ξ) = X (1 / 2 - ξ)) ∧
    (∀ x : ℝ, x ∉ Ioo 0 1 → 1 ≤ (X x).re) := by
  have hT := (proposition_5_3 N hN hlarge hGRH ha).2.2.2.2.2.1
  refine ⟨spectralQuaternion_zero N _, spectralQuaternion_one N _,
    spectralQuaternion_one_sub N _, spectralQuaternion_star N _ hT, ?_,
    spectralQuaternion_centered_even N _, spectralQuaternion_real_ge_one N _ hT⟩
  intro q
  rw [spectralQuaternion_one_sub, spectralQuaternion_star N _ hT]

end ConditionalGoldbach
