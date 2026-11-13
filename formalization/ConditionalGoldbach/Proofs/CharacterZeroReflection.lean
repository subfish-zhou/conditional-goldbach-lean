import ConditionalGoldbach.Proofs.CharacterZerosCompact

/-! Functional-equation reflection preserves the paper's zero multiplicities. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach

lemma gammaFactor_inv_differentiable {d : ℕ} (χ : Character d) :
    Differentiable ℂ (fun z => (χ.gammaFactor z)⁻¹) := by
  classical
  simp only [DirichletCharacter.gammaFactor]
  split_ifs
  · exact differentiable_Gammaℝ_inv
  · exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

lemma gammaFactor_ne_zero_re_pos {d : ℕ} (χ : Character d) {z : ℂ} (hz : 0 < z.re) :
    χ.gammaFactor z ≠ 0 := by
  classical
  simp only [DirichletCharacter.gammaFactor]
  split_ifs
  · exact Gammaℝ_ne_zero_of_re_pos hz
  · apply Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

lemma LFunction_order_eq_completed {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    {z : ℂ} (hz : 0 < z.re) :
    analyticOrderAt χ.LFunction z = analyticOrderAt χ.completedLFunction z := by
  have hd1 : d ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have he : χ.LFunction = χ.completedLFunction * (fun w => (χ.gammaFactor w)⁻¹) := by
    funext w
    simpa only [Pi.mul_apply, div_eq_mul_inv] using χ.LFunction_eq_completed_div_gammaFactor w (Or.inr hd1)
  rw [he, analyticOrderAt_mul ((χ.differentiable_completedLFunction hχ).analyticAt z)
    ((gammaFactor_inv_differentiable χ).analyticAt z)]
  rw [((gammaFactor_inv_differentiable χ).analyticAt z).analyticOrderAt_eq_zero.mpr
    (inv_ne_zero (gammaFactor_ne_zero_re_pos χ hz)), add_zero]

lemma primitive_rootNumber_ne_zero {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  have hL : χ.LFunction 3 ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
  have hC : χ.completedLFunction 3 ≠ 0 := by
    intro hh
    apply hL
    rw [χ.LFunction_eq_completed_div_gammaFactor 3 (Or.inl (by norm_num)), hh, zero_div]
  intro hzero
  have hh := hprim.completedLFunction_one_sub (-2)
  simp only [hzero, mul_zero, zero_mul] at hh
  apply hC
  convert hh using 1 <;> norm_num

lemma LFunction_order_reflection {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    analyticOrderAt χ.LFunction z = analyticOrderAt χ⁻¹.LFunction (1-z) := by
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  let g : ℂ → ℂ := fun u => 1-u
  let A : ℂ → ℂ := fun u => (d : ℂ)^(u-1/2)*χ.rootNumber
  have hg : AnalyticAt ℂ g (1-z) := analyticAt_const.sub analyticAt_id
  have hgd : deriv g (1-z) = -1 := by simpa only [g, id_eq] using ((hasDerivAt_id (1-z)).const_sub 1).deriv
  have hA : AnalyticAt ℂ A (1-z) :=
    (((differentiable_id.sub_const (1/2 : ℂ)).const_cpow (Or.inl hd0)).mul_const χ.rootNumber).analyticAt _
  have hAn : A (1-z) ≠ 0 := mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hd0))
    (primitive_rootNumber_ne_zero χ hχ hprim)
  have he : χ.completedLFunction ∘ g = A * χ⁻¹.completedLFunction := by
    funext u
    exact hprim.completedLFunction_one_sub u
  have hord := congrArg (fun f : ℂ → ℂ => analyticOrderAt f (1-z)) he
  rw [analyticOrderAt_comp_of_deriv_ne_zero hg (by rw [hgd]; norm_num),
    analyticOrderAt_mul hA ((χ⁻¹.differentiable_completedLFunction hinv).analyticAt (1-z)),
    hA.analyticOrderAt_eq_zero.mpr hAn, zero_add] at hord
  rw [LFunction_order_eq_completed χ hχ hz0,
    LFunction_order_eq_completed χ⁻¹ hinv (show 0 < (1-z).re by simp only [sub_re,one_re]; linarith)]
  simpa only [g, sub_sub_cancel] using hord

lemma LFunction_zero_reflection {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1)
    (hz : χ.LFunction z = 0) : χ⁻¹.LFunction (1-z) = 0 := by
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have he := LFunction_order_reflection χ hχ hprim hz0 hz1
  have han := (χ.differentiable_LFunction hχ).analyticAt z
  have han' := (χ⁻¹.differentiable_LFunction hinv).analyticAt (1-z)
  by_contra hn
  have hh := han'.analyticOrderAt_eq_zero.mpr hn
  rw [← he] at hh
  exact (han.analyticOrderAt_eq_zero.mp hh) hz

def reflectedZero {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (p : ZeroIndex χ) : ZeroIndex χ⁻¹ :=
  ⟨(1-p.val.1,p.val.2), by
    refine ⟨?_,?_,LFunction_zero_reflection χ hχ hprim p.property.1 p.property.2.1 p.property.2.2.1,?_⟩
    · simp only [sub_re,one_re]; linarith [p.property.2.1]
    · simp only [sub_re,one_re]; linarith [p.property.1]
    · have he := congrArg ENat.toNat (LFunction_order_reflection χ hχ hprim p.property.1 p.property.2.1)
      change p.val.2 < analyticOrderNatAt χ⁻¹.LFunction (1-p.val.1)
      rw [← show analyticOrderNatAt χ.LFunction p.val.1 = analyticOrderNatAt χ⁻¹.LFunction (1-p.val.1) from he]
      exact p.property.2.2.2⟩

lemma reflectedZero_injective {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) : Function.Injective (reflectedZero χ hχ hprim) := by
  intro p q he
  have hh := congrArg Subtype.val he
  have hfirst := congrArg Prod.fst hh
  have hsecond := congrArg Prod.snd hh
  apply Subtype.ext
  apply Prod.ext
  · change 1-p.val.1 = 1-q.val.1 at hfirst
    exact sub_right_injective hfirst
  · exact hsecond

end ConditionalGoldbach
