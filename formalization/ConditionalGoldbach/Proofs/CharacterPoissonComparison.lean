import ConditionalGoldbach.Proofs.CharacterPoissonIdentity
import ConditionalGoldbach.Proofs.CharacterPoissonAnchor
import ConditionalGoldbach.Proofs.CharacterHalfPlane
import ConditionalGoldbach.Proofs.GammaDifference
import ConditionalGoldbach.Proofs.CharacterEulerBounds

/-! The uniform logarithmic error between the positive zero sum and the real part of L'/L. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace ConditionalGoldbach
attribute [local instance] conductorNeZero

lemma Gamma_halfplane_horizontal_difference {x t : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line (3/2) t/2)‖ ≤ 6 := by
  have hu : (1/2:ℝ) ≤ (3/4+line x t/2).re := by simp [line]; linarith
  have hv : (1/2:ℝ) ≤ (3/4+line (3/2) t/2).re := by norm_num [line]
  have he : (3/4+line x t/2 : ℂ)-(3/4+line (3/2) t/2) = ((x/2-3/4:ℝ):ℂ) := by
    unfold line
    push_cast
    ring
  apply (Gamma_logDeriv_difference_norm_le hu hv).trans
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : x/2-3/4 ≤ 0)]
  linarith

lemma zeroPoisson_logDerivative_comparison : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∀ (_ : NeZero N), 4 ≤ N → GRH N → ∀χ ∈ oddCharacters N,
    ∀ x t : ℝ, 0 < x → x ≤ 1 →
      |zeroPoisson χ x t-(logDerivative χ (line x t)).re| ≤
        C*Real.log ((N:ℝ)*(|t|+2)) := by
  obtain ⟨C,hC,hQ⟩ := zeroPoisson_anchor_bound
  let B : ℝ := 3*(Real.log 4+4)+3
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C+B+8,by positivity,?_⟩
  intro N _ hN4 hGRH χ hχ x t hx hx1
  have hχn := odd_character_ne_one χ (Finset.mem_filter.mp hχ).2
  have he := zeroPoisson_logDerivative_difference hGRH χ hχ x (3/2) t hx (by norm_num)
  let W : ℂ := -logDerivative χ (line (3/2) t)+
    (logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line (3/2) t/2))/2-
    eulerCorrection χ (1/2+line x t)+eulerCorrection χ (1/2+line (3/2) t)
  have he' : zeroPoisson χ x t-(logDerivative χ (line x t)).re =
      zeroPoisson χ (3/2) t+W.re := by
    dsimp [W]
    simp only [add_re,sub_re,neg_re] at he ⊢
    linarith
  have hQ0 : 0 ≤ zeroPoisson χ (3/2) t := tsum_nonneg (fun _ => by positivity)
  have hW : ‖W‖ ≤ B+8*Real.log N := by
    have hg := logDerivative_right_bound N χ (line (3/2) t) (by norm_num [line])
    have hΓ := Gamma_halfplane_horizontal_difference (t := t) hx hx1
    have hE := eulerCorrection_norm_le χ (u := 1/2+line x t) (by simp [line]; exact hx.le)
    have hE' := eulerCorrection_norm_le χ (u := 1/2+line (3/2) t) (by norm_num [line])
    have hnorm := norm_add_le (-logDerivative χ (line (3/2) t))
      ((logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line (3/2) t/2))/2)
    have hnorm' := norm_sub_le (-logDerivative χ (line (3/2) t)+
      (logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line (3/2) t/2))/2)
      (eulerCorrection χ (1/2+line x t))
    have hnorm'' := norm_add_le (-logDerivative χ (line (3/2) t)+
      (logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line (3/2) t/2))/2-
      eulerCorrection χ (1/2+line x t)) (eulerCorrection χ (1/2+line (3/2) t))
    simp only [norm_neg,norm_div,Complex.norm_ofNat] at hnorm
    dsimp [W,B]
    linarith
  have hN : (4:ℝ) ≤ N := by exact_mod_cast hN4
  have hprod : (0:ℝ) < (N:ℝ)*(|t|+2) := by positivity
  have hlog : 1 ≤ Real.log ((N:ℝ)*(|t|+2)) := by
    apply (Real.le_log_iff_exp_le hprod).mpr
    have hlt := Real.exp_one_lt_three
    nlinarith [abs_nonneg t]
  have hlogN : Real.log N ≤ Real.log ((N:ℝ)*(|t|+2)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [abs_nonneg t]
  rw [he']
  calc
    _ ≤ |zeroPoisson χ (3/2) t|+|W.re| := abs_add_le _ _
    _ ≤ zeroPoisson χ (3/2) t+‖W‖ := by rw [abs_of_nonneg hQ0]; exact add_le_add_right (abs_re_le_norm W) _
    _ ≤ C*Real.log ((N:ℝ)*(|t|+2))+(B+8*Real.log N) :=
      add_le_add (hQ N inferInstance χ hχn t) hW
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlog hB.le]

end ConditionalGoldbach
