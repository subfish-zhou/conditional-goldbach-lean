module

public import ConditionalGoldbach.Proofs.HadamardLimit
public import ConditionalGoldbach.Proofs.CharacterGammaFactor
public import ConditionalGoldbach.Proofs.CharacterEulerCorrection
public import ConditionalGoldbach.Proofs.CharacterGrowth

/-! The paper's complete logarithmic-derivative expansion, with its primitive zeros and Euler corrections. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach
attribute [local instance] conductorNeZero

lemma logDerivative_zero_expansion {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) (s : ℂ) (hs : 0 < s.re) :
    logDerivative χ s = zeroDifference χ.primitiveCharacter (1/2+s) 2 +
      deriv χ.LFunction 2/χ.LFunction 2 -
      (deriv Gamma (3/4+s/2)/Gamma (3/4+s/2)-deriv Gamma (3/2)/Gamma (3/2))/2 +
      eulerCorrection χ (1/2+s)-eulerCorrection χ 2 := by
  have hodd := (Finset.mem_filter.mp hχ).2
  have hχn := odd_character_ne_one χ hodd
  have hχp := primitiveCharacter_ne_one_of_ne_one χ hχn
  have hoddp := primitiveCharacter_odd χ hodd
  have hu : 0 < (1/2+s).re := by norm_num; linarith
  have hLu : χ.primitiveCharacter.LFunction (1/2+s) ≠ 0 :=
    primitive_LFunction_ne_zero_of_GRH hGRH χ.conductor_dvd_level χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive hχp (by norm_num; exact hs)
  have hL2 : χ.primitiveCharacter.LFunction 2 ≠ 0 :=
    χ.primitiveCharacter.LFunction_ne_zero_of_one_le_re (Or.inl hχp) (by norm_num)
  have hCu : completedL χ.primitiveCharacter (1/2+s) ≠ 0 := by
    intro h
    exact hLu ((completedL_eq_zero_iff χ.primitiveCharacter hχp χ.primitiveCharacter_isPrimitive _).mp h).2.2
  have hC2 : completedL χ.primitiveCharacter 2 ≠ 0 := by
    intro h
    exact hL2 ((completedL_eq_zero_iff χ.primitiveCharacter hχp χ.primitiveCharacter_isPrimitive _).mp h).2.2
  have hH := completedL_logDerivative_difference χ.primitiveCharacter hχp
    χ.primitiveCharacter_isPrimitive (1/2+s) 2 hCu hC2
  change logDeriv (completedL χ.primitiveCharacter) (1/2+s) -
    logDeriv (completedL χ.primitiveCharacter) 2 = _ at hH
  rw [completedL_logDeriv_odd χ.primitiveCharacter hoddp hu hLu,
    completedL_logDeriv_odd χ.primitiveCharacter hoddp (by norm_num : 0<(2 : ℂ).re) hL2,
    show ((1/2+s : ℂ)+1)/2 = 3/4+s/2 by ring,
    show ((2 : ℂ)+1)/2 = 3/2 by ring] at hH
  have hEu := logDeriv_eq_primitive_add_euler χ hχn hu hLu
  have hE2 := logDeriv_eq_primitive_add_euler χ hχn (by norm_num : 0<(2 : ℂ).re) hL2
  change logDeriv χ.LFunction (1/2+s) = _
  change logDeriv χ.LFunction (1/2+s) = zeroDifference χ.primitiveCharacter (1/2+s) 2 +
      logDeriv χ.LFunction 2 -
      (deriv Gamma (3/4+s/2)/Gamma (3/4+s/2)-deriv Gamma (3/2)/Gamma (3/2))/2 +
      eulerCorrection χ (1/2+s)-eulerCorrection χ 2
  linear_combination hEu-hE2+hH

theorem lemma_3_4 (δ M : ℝ) (hδ : 0 < δ) (hM : δ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), 4 ≤ N → Even N → GRH N →
      ∀ χ ∈ oddCharacters N,
      (∀ s : ℂ, 0 < s.re → logDerivative χ s =
        zeroDifference χ.primitiveCharacter (1 / 2 + s) 2 +
        deriv χ.LFunction 2 / χ.LFunction 2 -
        (deriv Gamma (3 / 4 + s / 2) / Gamma (3 / 4 + s / 2) -
          deriv Gamma (3 / 2) / Gamma (3 / 2)) / 2 +
        eulerCorrection χ (1 / 2 + s) - eulerCorrection χ 2) ∧
      (∀ σ ∈ Icc δ M, ∀ t : ℝ,
        ‖logDerivative χ (line σ t)‖ ≤ C * Real.log (N * (|t| + 2)) ^ 2) := by
  obtain ⟨C,hC,hbound⟩ := logDerivative_uniform_bound δ M hδ hM
  refine ⟨C,hC,fun N _ hN4 _ hGRH χ hχ => ?_⟩
  exact ⟨logDerivative_zero_expansion hGRH χ hχ,
    hbound N inferInstance hN4 hGRH χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2)⟩

end ConditionalGoldbach
