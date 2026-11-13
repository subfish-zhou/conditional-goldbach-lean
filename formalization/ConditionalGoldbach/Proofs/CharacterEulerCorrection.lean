import ConditionalGoldbach.Proofs.CharacterZeroReflection

/-! Exact finite Euler corrections between a character and its primitive conductor. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach
attribute [local instance] conductorNeZero

lemma euler_factor_logDeriv {d : ℕ} [NeZero d] (χ : Character d)
    (p : ℕ) (hp : p.Prime) {u : ℂ} (hu : 0 < u.re) :
    logDeriv (fun z : ℂ => 1-χ p*(p : ℂ)^(-z)) u =
      χ p*(Real.log p : ℂ)/((p : ℂ)^u-χ p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : (p : ℂ)^u ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp0)
  have hf := eulerFactor_ne_zero χ hp hu
  have hden : (p : ℂ)^u-χ p ≠ 0 := by
    intro h
    apply hf
    rw [← sub_eq_zero.mp h,Complex.cpow_neg]
    field_simp
    ring
  have hd := (((hasDerivAt_id u).neg.const_cpow (Or.inl hp0)).const_mul (χ p)).const_sub 1
  simp only [Pi.neg_apply,id_eq] at hd
  rw [logDeriv_apply,hd.deriv,Complex.cpow_neg]
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast,Complex.ofReal_log (Nat.cast_nonneg p)]
  rw [hlog]
  field_simp

lemma primitiveCharacter_odd {N : ℕ} [NeZero N] (χ : Character N) (hodd : χ (-1) = -1) :
    χ.primitiveCharacter (-1) = -1 := by
  have he := χ.primitiveCharacter_apply_of_isCoprime (a := -1) (IsCoprime.neg_left (isCoprime_one_left))
  simp only [Int.cast_neg,Int.cast_one] at he
  exact he.trans hodd

lemma logDeriv_eq_primitive_add_euler {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1)
    {u : ℂ} (hu : 0 < u.re) (hprim : χ.primitiveCharacter.LFunction u ≠ 0) :
    logDeriv χ.LFunction u = logDeriv χ.primitiveCharacter.LFunction u + eulerCorrection χ u := by
  classical
  have hχp := primitiveCharacter_ne_one_of_ne_one χ hχ
  let F : ℕ → ℂ → ℂ := fun p z => 1-χ.primitiveCharacter p*(p : ℂ)^(-z)
  let P : ℂ → ℂ := ∏ p ∈ N.primeFactors, F p
  have hF (p : ℕ) (hp : p ∈ N.primeFactors) : Differentiable ℂ (F p) := by
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact ((differentiable_id.neg.const_cpow (Or.inl hp0)).const_mul _).const_sub 1
  have hFn (p : ℕ) (hp : p ∈ N.primeFactors) : F p u ≠ 0 :=
    eulerFactor_ne_zero χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hu
  have hP : Differentiable ℂ P := Differentiable.finsetProd (fun p hp => hF p hp)
  have hPn : P u ≠ 0 := by simpa only [P,Finset.prod_apply] using Finset.prod_ne_zero_iff.mpr hFn
  have he : χ.LFunction = χ.primitiveCharacter.LFunction*P := by
    funext z
    have hh := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (Or.inl hχp) (s := z)
    simpa only [χ.changeLevel_primitiveCharacter,P,F,Finset.prod_apply,Pi.mul_apply] using hh
  rw [he,logDeriv_mul u hprim hPn (χ.primitiveCharacter.differentiable_LFunction hχp u) (hP u)]
  congr 1
  change logDeriv (∏ p ∈ N.primeFactors, F p) u = _
  rw [logDeriv_prod hFn (fun p hp => hF p hp u)]
  unfold eulerCorrection
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  rw [euler_factor_logDeriv χ.primitiveCharacter p hprime hu]
  by_cases hpc : p ∣ χ.conductor
  · have hz : χ.primitiveCharacter p = 0 := χ.primitiveCharacter.map_nonunit (by
      rw [ZMod.isUnit_iff_coprime,Nat.Prime.coprime_iff_not_dvd hprime]
      exact not_not_intro hpc)
    simp [hpc,hz]
  · simp [hpc]

end ConditionalGoldbach
