import LiLiuGoldbach.Proofs.CharacterZeroExpansion

/-! Exact real-part identities relating the positive Poisson zero sum to L'/L. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace LiLiuGoldbach16
attribute [local instance] conductorNeZero

lemma zero_resolvent_real (ρ : ℂ) (hρ : ρ.re = 1/2) (x t : ℝ) :
    (1/((1/2:ℂ)+line x t-ρ)).re = x/(x^2+(t-ρ.im)^2) := by
  simp [one_div,Complex.inv_re,Complex.normSq_apply,line,hρ,pow_two]

lemma zeroDifference_real_eq_poisson {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ≠ 1) (x y t : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (zeroDifference χ.primitiveCharacter (1/2+line x t) (1/2+line y t)).re =
      zeroPoisson χ x t-zeroPoisson χ y t := by
  have hχp := primitiveCharacter_ne_one_of_ne_one χ hχ
  have hL (a : ℝ) (ha : 0 < a) : χ.primitiveCharacter.LFunction (1/2+line a t) ≠ 0 :=
    primitive_LFunction_ne_zero_of_GRH hGRH χ.conductor_dvd_level χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive hχp (by simp [line]; exact ha)
  have hC (a : ℝ) (ha : 0 < a) : completedL χ.primitiveCharacter (1/2+line a t) ≠ 0 := by
    intro he
    exact hL a ha ((completedL_eq_zero_iff χ.primitiveCharacter hχp χ.primitiveCharacter_isPrimitive _).mp he).2.2
  have hs := (primitive_zero_difference_summable_norm χ.primitiveCharacter hχp
    χ.primitiveCharacter_isPrimitive _ _ (hC x hx) (hC y hy)).of_norm
  rw [zeroDifference,Complex.re_tsum hs]
  have he : ∀p : ZeroIndex χ.primitiveCharacter,
      (1/(1/2+line x t-p.val.1)-1/(1/2+line y t-p.val.1)).re =
        x/(x^2+(t-p.val.1.im)^2)-y/(y^2+(t-p.val.1.im)^2) := by
    intro p
    have hre := hGRH χ.conductor inferInstance χ.conductor_dvd_level χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive p.val.1 p.property.1 p.property.2.1 p.property.2.2.1
    rw [sub_re,zero_resolvent_real _ hre,zero_resolvent_real _ hre]
  simp_rw [he]
  exact (primitive_zero_poisson_summable _ hχp χ.primitiveCharacter_isPrimitive _ _ hx).tsum_sub
    (primitive_zero_poisson_summable _ hχp χ.primitiveCharacter_isPrimitive _ _ hy)

lemma zeroPoisson_logDerivative_difference {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (x y t : ℝ) (hx : 0 < x) (hy : 0 < y) :
    zeroPoisson χ x t-zeroPoisson χ y t =
      (logDerivative χ (line x t)-logDerivative χ (line y t)+
        (logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line y t/2))/2-
        eulerCorrection χ (1/2+line x t)+eulerCorrection χ (1/2+line y t)).re := by
  have hodd := (Finset.mem_filter.mp hχ).2
  have hχn := odd_character_ne_one χ hodd
  have hχp := primitiveCharacter_ne_one_of_ne_one χ hχn
  have hoddp := primitiveCharacter_odd χ hodd
  have hu (a : ℝ) (ha : 0 < a) : 0 < (1/2+line a t).re := by simp [line]; linarith
  have hL (a : ℝ) (ha : 0 < a) : χ.primitiveCharacter.LFunction (1/2+line a t) ≠ 0 :=
    primitive_LFunction_ne_zero_of_GRH hGRH χ.conductor_dvd_level χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive hχp (by simp [line]; exact ha)
  have hC (a : ℝ) (ha : 0 < a) : completedL χ.primitiveCharacter (1/2+line a t) ≠ 0 := by
    intro he
    exact hL a ha ((completedL_eq_zero_iff χ.primitiveCharacter hχp χ.primitiveCharacter_isPrimitive _).mp he).2.2
  have hH := completedL_logDerivative_difference χ.primitiveCharacter hχp
    χ.primitiveCharacter_isPrimitive _ _ (hC x hx) (hC y hy)
  change logDeriv (completedL χ.primitiveCharacter) _ - logDeriv (completedL χ.primitiveCharacter) _ = _ at hH
  rw [completedL_logDeriv_odd χ.primitiveCharacter hoddp (hu x hx) (hL x hx),
    completedL_logDeriv_odd χ.primitiveCharacter hoddp (hu y hy) (hL y hy),
    show ((1/2+line x t : ℂ)+1)/2 = 3/4+line x t/2 by ring,
    show ((1/2+line y t : ℂ)+1)/2 = 3/4+line y t/2 by ring] at hH
  have hEx := logDeriv_eq_primitive_add_euler χ hχn (hu x hx) (hL x hx)
  have hEy := logDeriv_eq_primitive_add_euler χ hχn (hu y hy) (hL y hy)
  have he : logDerivative χ (line x t)-logDerivative χ (line y t)+
        (logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line y t/2))/2-
        eulerCorrection χ (1/2+line x t)+eulerCorrection χ (1/2+line y t) =
      zeroDifference χ.primitiveCharacter (1/2+line x t) (1/2+line y t) := by
    change logDeriv χ.LFunction (1/2+line x t)-logDeriv χ.LFunction (1/2+line y t)+
        (logDeriv Gamma (3/4+line x t/2)-logDeriv Gamma (3/4+line y t/2))/2-
        eulerCorrection χ (1/2+line x t)+eulerCorrection χ (1/2+line y t) = _
    change _ = zeroDifference χ.primitiveCharacter _ _ at hH
    change _ = _ at hEx hEy
    simp only [logDeriv_apply] at *
    linear_combination hH+hEx-hEy
  rw [he,zeroDifference_real_eq_poisson hGRH χ hχn x y t hx hy]

end LiLiuGoldbach16
