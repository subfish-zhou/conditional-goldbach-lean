import LiLiuGoldbach.Proofs.CharacterZeroReflection

/-! The completed function is entire and has exactly the multiplicity-indexed nontrivial zeros. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace LiLiuGoldbach16

lemma completedL_differentiable {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1) :
    Differentiable ℂ (completedL χ) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  exact (((differentiable_id.add_const 1).div_const 2).const_cpow (Or.inl hd)).mul
    (χ.differentiable_completedLFunction hχ)

lemma completedLFunction_ne_zero_right {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    {u : ℂ} (hu : 1 ≤ u.re) : χ.completedLFunction u ≠ 0 := by
  have hL := χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hu
  have hu0 : u ≠ 0 := by intro he; rw [he,zero_re] at hu; norm_num at hu
  intro hz
  apply hL
  rw [χ.LFunction_eq_completed_div_gammaFactor u (Or.inl hu0),hz,zero_div]

lemma completedLFunction_ne_zero_left {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {u : ℂ} (hu : u.re ≤ 0) :
    χ.completedLFunction u ≠ 0 := by
  have hh := hprim.completedLFunction_one_sub (1-u)
  rw [sub_sub_cancel] at hh
  rw [hh]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  exact mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hd))
    (primitive_rootNumber_ne_zero χ hχ hprim))
    (completedLFunction_ne_zero_right χ⁻¹ (inv_ne_one.mpr hχ)
      (by simp only [sub_re,one_re]; linarith))

lemma completedL_eq_zero_iff {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (u : ℂ) :
    completedL χ u = 0 ↔ 0 < u.re ∧ u.re < 1 ∧ χ.LFunction u = 0 := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hpow : (d : ℂ)^((u+1)/2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hd)
  rw [completedL,mul_eq_zero,or_iff_right hpow]
  constructor
  · intro hz
    have h0 : 0 < u.re := by
      by_contra h
      exact completedLFunction_ne_zero_left χ hχ hprim (le_of_not_gt h) hz
    have h1 : u.re < 1 := by
      by_contra h
      exact completedLFunction_ne_zero_right χ hχ (le_of_not_gt h) hz
    refine ⟨h0,h1,?_⟩
    rw [χ.LFunction_eq_completed_div_gammaFactor u
      (Or.inl (by intro he; rw [he,zero_re] at h0; exact lt_irrefl _ h0)),hz,zero_div]
  · rintro ⟨h0,h1,hz⟩
    have hu0 : u ≠ 0 := by intro he; rw [he,zero_re] at h0; exact lt_irrefl _ h0
    rw [χ.LFunction_eq_completed_div_gammaFactor u (Or.inl hu0)] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right (gammaFactor_ne_zero_re_pos χ h0)

lemma completedL_zero_ne_zero {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) : completedL χ 0 ≠ 0 := by
  intro h
  have hh := ((completedL_eq_zero_iff χ hχ hprim 0).mp h).1
  norm_num at hh

lemma completedL_order_eq_LFunction {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) {u : ℂ} (hu : 0 < u.re) :
    analyticOrderAt (completedL χ) u = analyticOrderAt χ.LFunction u := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hp : AnalyticAt ℂ (fun z : ℂ => (d : ℂ)^((z+1)/2)) u :=
    (((differentiable_id.add_const 1).div_const 2).const_cpow (Or.inl hd)).analyticAt u
  have hpn : (d : ℂ)^((u+1)/2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hd)
  change analyticOrderAt ((fun z : ℂ => (d : ℂ)^((z+1)/2))*χ.completedLFunction) u = _
  rw [analyticOrderAt_mul hp ((χ.differentiable_completedLFunction hχ).analyticAt u),
    hp.analyticOrderAt_eq_zero.mpr hpn,zero_add,LFunction_order_eq_completed χ hχ hu]

end LiLiuGoldbach16
