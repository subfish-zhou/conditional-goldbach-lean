import ConditionalGoldbach.Proofs.BaselineProductLink
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! The negative quadratic principal part of the continued arithmetic model. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Filter
namespace ConditionalGoldbach

lemma gammaQuotient_differentiableAt_zero_real {s : ℂ} (hs : s.re = 0) :
    DifferentiableAt ℂ gammaQuotient s := by
  have ha : 0 < ((3/2-s)/2).re := by norm_num [hs]
  have hb : 0 < ((3/2+s)/2).re := by norm_num [hs]
  unfold gammaQuotient
  exact ((hasDerivAt_Gamma_of_re_pos ha).differentiableAt.comp s (by fun_prop)).div
    ((hasDerivAt_Gamma_of_re_pos hb).differentiableAt.comp s (by fun_prop))
    (Gamma_ne_zero_of_re_pos hb)

lemma gammaQuotient_imaginary_product (γ : ℝ) :
    gammaQuotient (line 0 γ)*gammaQuotient (conj (line 0 γ)) = 1 := by
  have he : conj (line 0 γ) = -line 0 γ := by simp [line]
  have ha : Gamma ((3/2-line 0 γ)/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num [line])
  have hb : Gamma ((3/2+line 0 γ)/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num [line])
  rw [he]
  unfold gammaQuotient
  rw [sub_neg_eq_add,← sub_eq_add_neg]
  rw [div_mul_div_comm,mul_comm (Gamma ((3/2+line 0 γ)/2)) (Gamma ((3/2-line 0 γ)/2)),div_self (mul_ne_zero ha hb)]

lemma continuedModel_double_pole (N : ℕ) (hN : Even N) (hpos : 0 < N) (γ : ℝ) :
    Tendsto (fun x : ℝ => (x:ℂ)^2*continuedModel N (line x γ) (conj (line x γ)))
      (𝓝[>] 0) (𝓝 (-1/4:ℂ)) := by
  let F : ℝ → ℂ := fun x => (-1/4:ℂ)*(singularSeries N:ℂ)*
    ((Real.pi:ℂ)/N)^(2*(x:ℂ))*baselineProductR N (2*(x:ℂ))*
    riemannZeta₁ (1+2*(x:ℂ))*riemannZeta₁ (1-2*(x:ℂ))*
    gammaQuotient (line x γ)*gammaQuotient (conj (line x γ))
  have hB : ContinuousAt (baselineProductR N) 0 :=
    ((baselineProductR_differentiableOn N).differentiableAt (x := (0:ℂ))
      ((isOpen_re_gt (-(1/4:ℝ))).mem_nhds (show -(1/4:ℝ)<(0:ℂ).re by norm_num))).continuousAt
  have hG : ContinuousAt gammaQuotient (line 0 γ) :=
    (gammaQuotient_differentiableAt_zero_real (s := line 0 γ) (by simp [line])).continuousAt
  have hG' : ContinuousAt gammaQuotient (conj (line 0 γ)) :=
    (gammaQuotient_differentiableAt_zero_real (s := conj (line 0 γ)) (by simp [line])).continuousAt
  have hbase : (Real.pi:ℂ)/(N:ℂ) ≠ 0 := div_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast hpos.ne')
  have hF : ContinuousAt F 0 := by
    have hcp : ContinuousAt (fun x : ℝ => ((Real.pi:ℂ)/N)^(2*(x:ℂ))) 0 :=
      (by fun_prop : ContinuousAt (fun x : ℝ => 2*(x:ℂ)) 0).const_cpow (Or.inl hbase)
    have hBb : ContinuousAt (fun x : ℝ => baselineProductR N (2*(x:ℂ))) 0 :=
      (show ContinuousAt (baselineProductR N) (2*((0:ℝ):ℂ)) by simpa using hB).comp
        (f := fun x : ℝ => 2*(x:ℂ)) (by fun_prop)
    have hZp : ContinuousAt (fun x : ℝ => riemannZeta₁ (1+2*(x:ℂ))) 0 :=
      differentiable_riemannZeta₁.continuous.continuousAt.comp (by fun_prop)
    have hZm : ContinuousAt (fun x : ℝ => riemannZeta₁ (1-2*(x:ℂ))) 0 :=
      differentiable_riemannZeta₁.continuous.continuousAt.comp (by fun_prop)
    exact (((((continuousAt_const.mul continuousAt_const).mul hcp).mul hBb).mul hZp).mul hZm).mul
      (hG.comp (f := fun x : ℝ => line x γ) (by unfold line; fun_prop)) |>.mul
      (hG'.comp (f := fun x : ℝ => conj (line x γ)) (by unfold line; fun_prop))
  have hF0 : F 0 = (-1/4:ℂ) := by
    dsimp [F]
    simp only [ofReal_zero,mul_zero,zero_add,sub_zero,add_zero,cpow_zero,mul_one,riemannZeta₁_one]
    calc
      _ = (-1/4:ℂ)*((singularSeries N:ℂ)*baselineProductR N 0)*
        (gammaQuotient (line 0 γ)*gammaQuotient (conj (line 0 γ))) := by ring
      _ = _ := by rw [baselineProductR_zero N hN hpos,gammaQuotient_imaginary_product]; ring
  rw [← hF0]
  apply hF.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 from ne_of_gt hx)
  have he : line x γ+conj (line x γ) = 2*(x:ℂ) := by simp [line]; ring
  have he' : 1-line x γ-conj (line x γ) = 1-2*(x:ℂ) := by rw [sub_sub,he]
  have hp : 1+2*(x:ℂ) ≠ (1:ℂ) := by simp [hx0]
  have hm : 1-2*(x:ℂ) ≠ (1:ℂ) := by simp [hx0]
  unfold continuedModel
  rw [he,he',densityEulerProduct_eq_zeta_baseline N hN hpos (by simp; exact hx),
    riemannZeta_eq_inv_sub_mul hp,riemannZeta_eq_inv_sub_mul hm]
  dsimp [F]
  simp only [add_sub_cancel_left,sub_sub_cancel_left]
  field_simp
  ring

end ConditionalGoldbach
