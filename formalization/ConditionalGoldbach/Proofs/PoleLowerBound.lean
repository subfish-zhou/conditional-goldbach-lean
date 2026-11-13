import ConditionalGoldbach.Proofs.PoleCharacterKernel
import ConditionalGoldbach.Proofs.PoleDiagonalComparison
import ConditionalGoldbach.Proofs.PoleZeta
import ConditionalGoldbach.Proofs.PoleModel
import ConditionalGoldbach.Proofs.VariableStripOperators
import ConditionalGoldbach.Proofs.HardyKernelResidual

/-! A convergent scalar lower bound for the varying-strip residual operator. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Filter
namespace ConditionalGoldbach

def poleLowerExpression (N : ℕ) [NeZero N] (γ x : ℝ) : ℝ :=
  2*Real.log N*((x:ℂ)^2*(characterKernel N (line x γ) (conj (line x γ))-
    deriv (logDeriv riemannZeta) (1+2*(x:ℂ))-
    continuedModel N (line x γ) (conj (line x γ)))).re / ((1+x)^2+γ^2)

lemma poleLowerExpression_tendsto (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N) (γ : ℝ) :
    Tendsto (poleLowerExpression N γ) (𝓝[>] 0)
      (𝓝 (2*poleCoefficient N γ*Real.log N/(1+γ^2))) := by
  have hP := characterKernel_double_pole (N := N) γ
  have hD := zeta_logDeriv_deriv_double_pole
  have hK := continuedModel_double_pole N hN (by omega) γ
  have hA := Complex.continuous_re.tendsto _ |>.comp ((hP.sub hD).sub hK)
  have hB : Tendsto (fun x : ℝ => (1+x)^2+γ^2) (𝓝[>] 0) (𝓝 (1+γ^2)) := by
    have hc : Continuous (fun x : ℝ => (1+x)^2+γ^2) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hh := (hA.const_mul (2*Real.log N)).div hB (by positivity : 1+γ^2 ≠ 0)
  convert hh using 1
  · funext x
    unfold poleLowerExpression
    congr 2
    rw [mul_sub,mul_sub]
    rfl
  · norm_num
    ring

lemma residual_real_lower_bound (N : ℕ) [NeZero N] {x : ℝ} (hx : 0 < x) (γ : ℝ) :
    (characterKernel N (line x γ) (conj (line x γ))-
      deriv (logDeriv riemannZeta) (1+2*(x:ℂ))-
      continuedModel N (line x γ) (conj (line x γ))).re ≤
      ‖residual N (line x γ) (conj (line x γ))‖ := by
  have hD := diagonalSeries_real_le_zeta_second N (w := 2*x) (by positivity)
  have he : line x γ+conj (line x γ) = 2*(x:ℂ) := by simp [line]; ring
  have hr := Complex.re_le_norm (residual N (line x γ) (conj (line x γ)))
  simp only [residual,sub_re,he] at hr
  push_cast at hD
  simp only [sub_re,residual,he]
  linarith

lemma poleLowerExpression_le_scaled_operator (N : ℕ) [NeZero N] (hN4 : 4 ≤ N)
    (hGRH : GRH N) (γ c : ℝ) (hc : 0 < c) (hcsmall : c < Real.log N/24)
    (ha : alpha N c < beta) :
    poleLowerExpression N γ (2*alpha N c) ≤ c*‖residualOperator ha N‖ := by
  let a : ℝ := alpha N c
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have ha0 : 0 < a := alpha_pos_at N hN4 c hc
  have ha24 : a < 1/24 := by
    dsimp [a,alpha]
    exact (div_lt_iff₀ hlog).mpr (by linarith)
  have hs : line (2*a) γ ∈ strip a beta := by
    change a < (line (2*a) γ).re ∧ (line (2*a) γ).re < beta
    simp only [line,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    unfold beta
    constructor <;> linarith
  have hd : pointDistance a beta (line (2*a) γ) = a := by
    unfold pointDistance beta
    simp only [line,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [min_eq_left (by linarith)]
    ring
  have hp := residualOperator_pairing_at a N ha0 hN4 hGRH ha _ _ hs hs
  have hb := residual_norm_le_of_kernel_pairing ha ha0.le N (residualOperator ha N) _ _ hs hs hp
  rw [hd,show a*a=a^2 by ring,Real.sqrt_sq ha0.le] at hb
  have hnorm : ‖1+line (2*a) γ‖^2 = (1+2*a)^2+γ^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,line,pow_two]
  have hden : 0 < (1+2*a)^2+γ^2 := by positivity
  have hl := residual_real_lower_bound N (x := 2*a) (by positivity) γ
  have hA : ((2*a:ℝ):ℂ)^2 = (((2*a)^2:ℝ):ℂ) := by simp
  unfold poleLowerExpression
  change 2*Real.log N*(((2*a:ℝ):ℂ)^2*(_)).re/((1+2*a)^2+γ^2) ≤ _
  rw [hA,Complex.re_ofReal_mul]
  have hb' : ‖residual N (line (2*a) γ) (conj (line (2*a) γ))‖ ≤
      ‖residualOperator ha N‖*((1+2*a)^2+γ^2)/(8*a) := by
    convert hb using 1
    rw [mul_assoc,← pow_two,hnorm]
  calc
    _ ≤ 2*Real.log N*((2*a)^2*‖residual N (line (2*a) γ) (conj (line (2*a) γ))‖)/((1+2*a)^2+γ^2) := by gcongr
    _ ≤ 2*Real.log N*((2*a)^2*(‖residualOperator ha N‖*((1+2*a)^2+γ^2)/(8*a)))/((1+2*a)^2+γ^2) := by gcongr
    _ = c*‖residualOperator ha N‖ := by
      have hac : a*Real.log N = c := div_mul_cancel₀ c hlog.ne'
      calc
        _ = (a*Real.log N)*‖residualOperator ha N‖ := by field_simp; ring
        _ = _ := by rw [hac]

lemma residualOperator_pole_liminf (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (γ : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c < c₀ →
      ∀ ha : alpha N c < beta,
        2*poleCoefficient N γ*Real.log N/(1+γ^2)-ε ≤ c*‖residualOperator ha N‖ := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hmap : Tendsto (fun c : ℝ => 2*alpha N c) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun c : ℝ => 2*alpha N c) := by unfold alpha; fun_prop
      simpa [alpha] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact mul_pos two_pos (alpha_pos_at N hN4 c hc)
  have hF := (poleLowerExpression_tendsto N hN hN4 γ).comp hmap
  intro ε hε
  have he := hF.eventually (eventually_gt_nhds (sub_lt_self _ hε))
  obtain ⟨δ,hδ,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨min δ (Real.log N/24),lt_min hδ (by positivity),?_⟩
  intro c hc hcδ ha
  exact (hbound ⟨hc,lt_of_lt_of_le hcδ (min_le_left _ _)⟩).le.trans
    (poleLowerExpression_le_scaled_operator N hN4 hGRH γ c hc
      (lt_of_lt_of_le hcδ (min_le_right _ _)) ha)

end ConditionalGoldbach
