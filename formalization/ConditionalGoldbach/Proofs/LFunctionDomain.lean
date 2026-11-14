module

public import ConditionalGoldbach.Definitions.Characters
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# L-function nonvanishing on the GRH half-plane

GRH is applied only to the primitive character at its conductor, whose divisibility
into the original modulus is explicit. Mathlib supplies nonvanishing on Re u ≥ 1.
The finite Euler product then transfers nonvanishing to an arbitrary nonprincipal
character at the original modulus. In particular, all odd characters are covered,
including imprimitive ones.

This module also proves analyticity of the logarithmic derivative and the joint
holomorphy clause of Proposition 3.2 under GRH. It does not claim the remaining
Dirichlet-series or joint meromorphic continuation clauses of that proposition.
-/

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

lemma odd_character_ne_one {N : ℕ} [NeZero N] (χ : Character N)
    (hχ : χ (-1) = -1) : χ ≠ 1 := by
  intro heq
  have ht : (1 : ℂ) = -1 := by
    simpa [heq, MulChar.one_apply isUnit_neg_one] using hχ
  norm_num at ht

/-- Induction from the conductor preserves nonprincipality in the needed direction. -/
lemma primitiveCharacter_ne_one_of_ne_one {N : ℕ} [NeZero N] (χ : Character N)
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro hprim
  apply hχ
  rw [← χ.changeLevel_primitiveCharacter, hprim, DirichletCharacter.changeLevel_one]

/-- The GRH hypothesis is used at the primitive level `d`, with `d ∣ N` retained. -/
lemma primitive_LFunction_ne_zero_in_strip_of_GRH {N d : ℕ} [NeZero d]
    (hGRH : GRH N) (hd : d ∣ N) (χ : Character d) (hχ : χ.IsPrimitive)
    {u : ℂ} (hu : 1 / 2 < u.re) (hu1 : u.re < 1) : χ.LFunction u ≠ 0 := by
  intro hzero
  have hzero_re := hGRH d inferInstance hd χ hχ u (by linarith) hu1 hzero
  linarith

/-- Nonprincipality also covers the point `u = 1` in the closed right half-plane. -/
lemma primitive_LFunction_ne_zero_of_GRH {N d : ℕ} [NeZero d]
    (hGRH : GRH N) (hd : d ∣ N) (χ : Character d) (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {u : ℂ} (hu : 1 / 2 < u.re) : χ.LFunction u ≠ 0 := by
  by_cases hu1 : 1 ≤ u.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ1) hu1
  · exact primitive_LFunction_ne_zero_in_strip_of_GRH hGRH hd χ hχ hu (lt_of_not_ge hu1)

/-- Every removed Euler factor is nonzero as soon as the argument has positive real part. -/
lemma eulerFactor_ne_zero {N : ℕ} [NeZero N] (χ : Character N)
    {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : 0 < u.re) :
    1 - χ p * (p : ℂ) ^ (-u) ≠ 0 := by
  have hnorm : ‖χ p * (p : ℂ) ^ (-u)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖χ p‖ * ‖(p : ℂ) ^ (-u)‖ ≤ 1 * ‖(p : ℂ) ^ (-u)‖ :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one p) (norm_nonneg _)
      _ = (p : ℝ) ^ (-u.re) := by
        rw [one_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  intro hzero
  have hone : χ p * (p : ℂ) ^ (-u) = 1 := (sub_eq_zero.mp hzero).symm
  rw [hone, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

/-- Transfer from the primitive conductor to the original, possibly imprimitive, character. -/
lemma LFunction_ne_zero_of_GRH {N : ℕ} [NeZero N]
    (hGRH : GRH N) (χ : Character N) (hχ : χ ≠ 1)
    {u : ℂ} (hu : 1 / 2 < u.re) : χ.LFunction u ≠ 0 := by
  have hprim : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one_of_ne_one χ hχ
  have hLprim := primitive_LFunction_ne_zero_of_GRH hGRH χ.conductor_dvd_level
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hprim hu
  have hprod : ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-u)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact eulerFactor_ne_zero χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp)
      (by linarith)
  rw [← χ.changeLevel_primitiveCharacter,
    DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
      (Or.inl hprim)]
  exact mul_ne_zero hLprim hprod

lemma odd_LFunction_ne_zero_of_GRH {N : ℕ} [NeZero N]
    (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    {u : ℂ} (hu : 1 / 2 < u.re) : χ.LFunction u ≠ 0 := by
  apply LFunction_ne_zero_of_GRH hGRH χ _ hu
  exact odd_character_ne_one χ (Finset.mem_filter.mp hχ).2

/-- The logarithmic derivative is analytic wherever the shifted L-function is nonzero. -/
lemma logDerivative_analyticAt_of_ne_zero {N : ℕ} [NeZero N]
    (χ : Character N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : χ.LFunction (1 / 2 + s) ≠ 0) : AnalyticAt ℂ (logDerivative χ) s := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + z) s :=
    analyticAt_const.add analyticAt_id
  have hL := DirichletCharacter.differentiable_LFunction hχ
  exact ((hL.deriv.analyticAt _).comp hshift).div ((hL.analyticAt _).comp hshift) hs

lemma logDerivative_analyticAt_of_GRH {N : ℕ} [NeZero N]
    (hGRH : GRH N) (χ : Character N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (logDerivative χ) s := by
  apply logDerivative_analyticAt_of_ne_zero χ hχ
  apply LFunction_ne_zero_of_GRH hGRH χ hχ
  norm_num
  linarith

lemma odd_logDerivative_analyticAt_of_GRH {N : ℕ} [NeZero N]
    (hGRH : GRH N) (χ : Character N) (hχ : χ ∈ oddCharacters N)
    {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (logDerivative χ) s := by
  exact logDerivative_analyticAt_of_GRH hGRH χ
    (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2) hs

/-- The actual two-variable kernel, including the conjugation in its second argument. -/
lemma characterKernel_differentiableOn_of_GRH {N : ℕ} [NeZero N]
    (hGRH : GRH N) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => characterKernel N p.1 p.2)
      {p | 0 < p.1.re ∧ 0 < p.2.re} := by
  intro p hp
  apply DifferentiableAt.differentiableWithinAt
  unfold characterKernel
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.fun_sum
  intro χ hχ
  have hfirst := (odd_logDerivative_analyticAt_of_GRH hGRH χ hχ hp.1).differentiableAt
  have hconj := (odd_logDerivative_analyticAt_of_GRH hGRH χ hχ
    (show 0 < (conj p.2).re by simpa using hp.2)).differentiableAt.conj_conj
  have hsecond : DifferentiableAt ℂ (fun z => conj (logDerivative χ (conj z))) p.2 := by
    simpa only [Function.comp_def, Complex.conj_conj] using hconj
  exact (hfirst.comp p differentiableAt_fst).mul (hsecond.comp p differentiableAt_snd)

end ConditionalGoldbach
