import ConditionalGoldbach.Proofs.BetaIdentity
import ConditionalGoldbach.Definitions

/-! Entire numerators and a common denominator for both beta-kernel formulas. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

private def betaDen (p : ℂ × ℂ) : ℂ :=
  (Gamma (1/2-p.1))⁻¹ * (Gamma (1/2-p.2))⁻¹ * (Gamma (p.1+p.2))⁻¹

private def betaNum (p : ℂ × ℂ) : ℂ :=
  (Gamma (1/2-p.2))⁻¹ * (Gamma ((1/2-p.1)+(p.1+p.2)))⁻¹ +
  (Gamma (1/2-p.1))⁻¹ * (Gamma ((1/2-p.2)+(p.1+p.2)))⁻¹ -
  (Gamma (p.1+p.2))⁻¹ * (Gamma ((1/2-p.1)+(1/2-p.2)))⁻¹

private def gammaDen (p : ℂ × ℂ) : ℂ :=
  (Gamma (p.1+p.2))⁻¹ * (Gamma ((3/2-p.1)/2))⁻¹ * (Gamma ((3/2-p.2)/2))⁻¹

private def gammaNum (p : ℂ × ℂ) : ℂ :=
  (2 : ℂ)^(1-(p.1+p.2)) * Complex.cos (Real.pi*(p.1+p.2)/2) *
  (Gamma ((3/2+p.1)/2))⁻¹ * (Gamma ((3/2+p.2)/2))⁻¹

private lemma betaDen_diff : Differentiable ℂ betaDen := by
  unfold betaDen
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact differentiable_one_div_Gamma.comp (by fun_prop)
    · exact differentiable_one_div_Gamma.comp (by fun_prop)
  · exact differentiable_one_div_Gamma.comp (by fun_prop)

private lemma betaNum_diff : Differentiable ℂ betaNum := by
  unfold betaNum
  apply Differentiable.sub
  · apply Differentiable.add <;> apply Differentiable.mul <;>
      exact differentiable_one_div_Gamma.comp (by fun_prop)
  · apply Differentiable.mul <;> exact differentiable_one_div_Gamma.comp (by fun_prop)

private lemma gammaDen_diff : Differentiable ℂ gammaDen := by
  unfold gammaDen
  apply Differentiable.mul
  · apply Differentiable.mul <;> exact differentiable_one_div_Gamma.comp (by fun_prop)
  · exact differentiable_one_div_Gamma.comp (by fun_prop)

private lemma gammaNum_diff : Differentiable ℂ gammaNum := by
  unfold gammaNum
  apply Differentiable.mul
  · apply Differentiable.mul
    · apply Differentiable.mul
      · exact (by fun_prop : Differentiable ℂ (fun p : ℂ × ℂ => 1-(p.1+p.2))).const_cpow (by norm_num)
      · fun_prop
    · exact differentiable_one_div_Gamma.comp (by fun_prop)
  · exact differentiable_one_div_Gamma.comp (by fun_prop)

private lemma betaDen_ne {p : ℂ × ℂ} (hp : p ∈ betaDomain) : betaDen p ≠ 0 := by
  have ha : 0 < (1/2-p.1).re := by simp; linarith [hp.1]
  have hb : 0 < (1/2-p.2).re := by simp; linarith [hp.2.1]
  have hc : 0 < (p.1+p.2).re := hp.2.2
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Gamma_ne_zero_of_re_pos ha))
    (inv_ne_zero (Gamma_ne_zero_of_re_pos hb))) (inv_ne_zero (Gamma_ne_zero_of_re_pos hc))

private lemma gammaDen_ne {p : ℂ × ℂ} (hp : p ∈ betaDomain) : gammaDen p ≠ 0 := by
  have ha : 0 < ((3/2-p.1)/2).re := by simp; linarith [hp.1]
  have hb : 0 < ((3/2-p.2)/2).re := by simp; linarith [hp.2.1]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Gamma_ne_zero_of_re_pos hp.2.2))
    (inv_ne_zero (Gamma_ne_zero_of_re_pos ha))) (inv_ne_zero (Gamma_ne_zero_of_re_pos hb))

private lemma betaNum_div {p : ℂ × ℂ} (hp : betaDen p ≠ 0) :
    betaGamma (1/2-p.1) (p.1+p.2) + betaGamma (1/2-p.2) (p.1+p.2) -
    betaGamma (1/2-p.1) (1/2-p.2) = betaNum p / betaDen p := by
  have ha : Gamma (1/2-p.1) ≠ 0 := by
    simpa using (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1
  have hb : Gamma (1/2-p.2) ≠ 0 := by
    simpa using (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2
  have hc : Gamma (p.1+p.2) ≠ 0 := by
    simpa using (mul_ne_zero_iff.mp hp).2
  have halg (a b c d e f : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
      a*c*d+b*c*e-a*b*f = (b⁻¹*d+a⁻¹*e-c⁻¹*f)*(a*b*c) := by
    field_simp
  simp only [betaGamma, betaNum, betaDen, div_eq_mul_inv, mul_inv, inv_inv]
  exact halg _ _ _ _ _ _ ha hb hc

private lemma gammaNum_div {p : ℂ × ℂ} (hp : gammaDen p ≠ 0) :
    (2 : ℂ)^(1-(p.1+p.2)) * Gamma (p.1+p.2) *
      Complex.cos (Real.pi*(p.1+p.2)/2) * gammaQuotient p.1 * gammaQuotient p.2 =
      gammaNum p / gammaDen p := by
  unfold gammaNum gammaDen gammaQuotient
  simp only [mul_inv, inv_inv, div_eq_mul_inv]
  ring

private lemma betaGamma_identity {p : ℂ × ℂ} (hp : p ∈ betaDomain) :
    betaGamma (1/2-p.1) (p.1+p.2) + betaGamma (1/2-p.2) (p.1+p.2) -
    betaGamma (1/2-p.1) (1/2-p.2) =
    (2 : ℂ)^(1-(p.1+p.2)) * Gamma (p.1+p.2) *
      Complex.cos (Real.pi*(p.1+p.2)/2) * gammaQuotient p.1 * gammaQuotient p.2 := by
  have ha : 0 < (1/2-p.1).re := by simp; linarith [hp.1]
  have hb : 0 < (1/2-p.2).re := by simp; linarith [hp.2.1]
  have h := betaKernel_gamma_identity p.1 p.2 hp
  dsimp [betaKernel] at h
  rw [betaIntegral_eq_Gamma_mul_div _ _ ha hp.2.2,
    betaIntegral_eq_Gamma_mul_div _ _ hb hp.2.2,
    betaIntegral_eq_Gamma_mul_div _ _ ha hb] at h
  exact h

private lemma betaNum_cross (p : ℂ × ℂ) :
    betaNum p*gammaDen p = gammaNum p*betaDen p := by
  let p₀ : ℂ × ℂ := (1/4,1/4)
  let l : ℂ → ℂ × ℂ := fun t => p₀+t • (p-p₀)
  have hl : Differentiable ℂ l := by fun_prop
  have hF : AnalyticOnNhd ℂ (fun t => betaNum (l t)*gammaDen (l t)) univ :=
    fun z _ => ((betaNum_diff.mul gammaDen_diff).comp hl).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun t => gammaNum (l t)*betaDen (l t)) univ :=
    fun z _ => ((gammaNum_diff.mul betaDen_diff).comp hl).analyticAt z
  have ho : IsOpen betaDomain := by
    unfold betaDomain
    exact (isOpen_lt (Complex.continuous_re.comp continuous_fst) continuous_const).inter
      ((isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_fst.add continuous_snd))))
  have h₀ : l 0 ∈ betaDomain := by norm_num [l, p₀, betaDomain]
  have he := hF.eq_of_eventuallyEq hG (z₀ := (0 : ℂ)) (by
    filter_upwards [hl.continuous.continuousAt.eventually (ho.mem_nhds h₀)] with t ht
    have h := (betaNum_div (betaDen_ne ht)).symm.trans
      ((betaGamma_identity ht).trans (gammaNum_div (gammaDen_ne ht)))
    exact (div_eq_div_iff (betaDen_ne ht) (gammaDen_ne ht)).mp h)
  simpa [l] using congrFun he 1

theorem lemma_4_2_meromorphic :
    ∃ A B : ℂ × ℂ → ℂ,
      Differentiable ℂ A ∧ Differentiable ℂ B ∧ B ≠ 0 ∧
      ∀ p : ℂ × ℂ, B p ≠ 0 →
        betaGamma (1 / 2 - p.1) (p.1 + p.2) +
          betaGamma (1 / 2 - p.2) (p.1 + p.2) -
          betaGamma (1 / 2 - p.1) (1 / 2 - p.2) = A p / B p ∧
        (2 : ℂ) ^ (1 - (p.1 + p.2)) * Gamma (p.1 + p.2) *
          Complex.cos (Real.pi * (p.1 + p.2) / 2) *
          gammaQuotient p.1 * gammaQuotient p.2 = A p / B p := by
  refine ⟨fun p => betaNum p*gammaDen p, fun p => betaDen p*gammaDen p,
    betaNum_diff.mul gammaDen_diff, betaDen_diff.mul gammaDen_diff, ?_, ?_⟩
  · intro he
    have hp : ((1/4 : ℂ),(1/4 : ℂ)) ∈ betaDomain := by norm_num [betaDomain]
    have hn := mul_ne_zero (betaDen_ne hp) (gammaDen_ne hp)
    exact hn (congrFun he ((1/4 : ℂ),(1/4 : ℂ)))
  · intro p hp
    have hb := (mul_ne_zero_iff.mp hp).1
    have hg := (mul_ne_zero_iff.mp hp).2
    dsimp only
    constructor
    · rw [mul_div_mul_right _ _ hg]
      exact betaNum_div hb
    · rw [betaNum_cross p, mul_comm (betaDen p), mul_div_mul_right _ _ hb]
      exact gammaNum_div hg

end ConditionalGoldbach
