module

public import ConditionalGoldbach.Proofs.CompletedLZeros

/-! Exact logarithmic derivatives of the completed odd-character Gamma factors. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach

lemma logDeriv_cpow_affine (c a b z : ℂ) (hc : c ≠ 0) :
    logDeriv (fun w : ℂ => c^(a*w+b)) z = a*Complex.log c := by
  have hd := (((hasDerivAt_id z).const_mul a).add_const b).const_cpow (Or.inl hc)
  simp only [id_eq] at hd
  rw [logDeriv_apply,hd.deriv]
  have hp : c^(a*z+b) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  field_simp

lemma completedL_odd_formula {d : ℕ} [NeZero d] (χ : Character d)
    (hodd : χ (-1) = -1) {z : ℂ} (hz : 0 < z.re) :
    completedL χ z = (d : ℂ)^((z+1)/2) * (Real.pi : ℂ)^(-(z+1)/2) *
      Gamma ((z+1)/2) * χ.LFunction z := by
  have hz0 : z ≠ 0 := by intro he; rw [he,zero_re] at hz; exact lt_irrefl _ hz
  have hγ := gammaFactor_ne_zero_re_pos χ hz
  have he := (eq_div_iff hγ).mp (χ.LFunction_eq_completed_div_gammaFactor z (Or.inl hz0))
  rw [completedL,← he,DirichletCharacter.Odd.gammaFactor_def hodd,Complex.Gammaℝ_def]
  ring

lemma completedL_logDeriv_odd {d : ℕ} [NeZero d] (χ : Character d)
    (hodd : χ (-1) = -1) {z : ℂ} (hz : 0 < z.re) (hL : χ.LFunction z ≠ 0) :
    logDeriv (completedL χ) z = logDeriv χ.LFunction z +
      (Complex.log (d : ℂ)-Complex.log (Real.pi : ℂ))/2 +
      (deriv Gamma ((z+1)/2)/Gamma ((z+1)/2))/2 := by
  have hχ := odd_character_ne_one χ hodd
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓre : 0 < ((z+1)/2).re := by simp only [div_ofNat_re,add_re,one_re]; linarith
  have hΓ := Gamma_ne_zero_of_re_pos hΓre
  have hΓd := (Complex.hasDerivAt_Gamma_of_re_pos hΓre).differentiableAt
  let P : ℂ → ℂ := fun w => (d : ℂ)^((w+1)/2)
  let Q : ℂ → ℂ := fun w => (Real.pi : ℂ)^(-(w+1)/2)
  let G : ℂ → ℂ := fun w => Gamma ((w+1)/2)
  have hP : Differentiable ℂ P := (((differentiable_id.add_const 1).div_const 2).const_cpow (Or.inl hd))
  have hQ : Differentiable ℂ Q := ((((differentiable_id.add_const 1).neg).div_const 2).const_cpow (Or.inl hπ))
  have hGd := hΓd.hasDerivAt.comp z (((hasDerivAt_id z).add_const 1).div_const 2)
  simp only [Function.comp_def,id_eq] at hGd
  have hGn : G z ≠ 0 := hΓ
  have hG : DifferentiableAt ℂ G z := hGd.differentiableAt
  have hPn : P z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hd)
  have hQn : Q z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have he : completedL χ =ᶠ[𝓝 z] P*Q*G*χ.LFunction := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact completedL_odd_formula χ hodd hw
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_mul (f := P*Q*G) (g := χ.LFunction) z (mul_ne_zero (mul_ne_zero hPn hQn) hGn) hL ((hP z).mul (hQ z)|>.mul hG) (χ.differentiable_LFunction hχ z),
    logDeriv_mul (f := P*Q) (g := G) z (mul_ne_zero hPn hQn) hGn ((hP z).mul (hQ z)) hG,
    logDeriv_mul (f := P) (g := Q) z hPn hQn (hP z) (hQ z)]
  have hPe : P = fun w : ℂ => (d : ℂ)^((1/2)*w+1/2) := by funext w; dsimp [P]; congr 1; ring
  have hQe : Q = fun w : ℂ => (Real.pi : ℂ)^((-1/2)*w+(-1/2)) := by funext w; dsimp [Q]; congr 1; ring
  rw [hPe,hQe,logDeriv_cpow_affine _ _ _ _ hd,logDeriv_cpow_affine _ _ _ _ hπ]
  have hGe : logDeriv G z = (deriv Gamma ((z+1)/2)/Gamma ((z+1)/2))/2 := by
    rw [logDeriv_apply,hGd.deriv]
    dsimp [G]
    ring
  rw [hGe]
  ring

end ConditionalGoldbach
