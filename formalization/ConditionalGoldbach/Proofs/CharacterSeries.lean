module

public import ConditionalGoldbach.Proofs.Characters
public import ConditionalGoldbach.Proofs.LFunctionDomain

/-! Absolutely convergent Dirichlet expansions, with the original odd-character projector. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

lemma logDerivative_eq_neg_tsum {N : ℕ} [NeZero N] (χ : Character N)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    logDerivative χ s = -∑' n : ℕ,
      (mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 + s) := by
  have hs' : 1 < (1 / 2 + s).re := by norm_num; linarith
  rw [logDerivative, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs',
    DirichletCharacter.LFunction_eq_LSeries χ hs']
  have heq := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs'
  rw [neg_div] at heq
  calc
    _ = -LSeries ((fun n : ℕ => χ n) * fun n => (mangoldt n : ℂ)) (1 / 2 + s) := by rw [heq]; ring
    _ = _ := by
      congr 1
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · subst n
        simp [LSeries.term, mangoldt]
      · simp only [LSeries.term, hn, ite_false, Pi.mul_apply]
        congr 1
        ring

lemma summable_logDerivative_terms {N : ℕ} [NeZero N] (χ : Character N)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun n : ℕ => (mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 + s)) := by
  have hs' : 1 < (1 / 2 + s).re := by norm_num; linarith
  apply (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs').congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, mangoldt]
  · simp only [LSeries.term, hn, ite_false, Pi.mul_apply]
    congr 1
    ring

lemma conj_natCast_cpow (n : ℕ) (z : ℂ) :
    conj ((n : ℂ) ^ z) = (n : ℂ) ^ conj z := by
  simpa using (Complex.conj_cpow (n : ℂ) (conj z)
    (by rw [Complex.natCast_arg]; exact ne_of_lt Real.pi_pos)).symm

lemma conjugate_logDerivative_eq_neg_tsum {N : ℕ} [NeZero N] (χ : Character N)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    conj (logDerivative χ (conj z)) = -∑' m : ℕ,
      (mangoldt m : ℂ) * conj (χ m) / (m : ℂ) ^ (1 / 2 + z) := by
  rw [logDerivative_eq_neg_tsum χ (by simpa using hz), map_neg, Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro m
  simp [map_div₀, map_mul, conj_natCast_cpow, show conj (2 : ℂ) = 2 from Complex.conj_ofReal 2]

/-- GRH rewrites each actual zero, preserving its multiplicity index. -/
theorem lemma_3_4_paired_zero_sum (N : ℕ) [NeZero N]
    (_hN : Even N) (_hN4 : 4 ≤ N) (hGRH : GRH N)
    (χ : Character N) (_hχ : χ ∈ oddCharacters N) (s : ℂ) (_hs : 0 < s.re) :
    zeroDifference χ.primitiveCharacter (1 / 2 + s) 2 = pairedZeroSum χ s := by
  unfold zeroDifference pairedZeroSum
  apply tsum_congr
  intro p
  have hr : p.val.1.re = 1 / 2 := hGRH χ.conductor inferInstance
    χ.conductor_dvd_level χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      p.val.1 p.property.1 p.property.2.1 p.property.2.2.1
  have hρ : p.val.1 = 1 / 2 + p.val.1.im * I := by
    apply Complex.ext <;> simp [hr]
  conv_lhs => rw [hρ]
  congr 2 <;> ring

lemma summable_conjugate_logDerivative_terms {N : ℕ} [NeZero N] (χ : Character N)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    Summable (fun m : ℕ => (mangoldt m : ℂ) * conj (χ m) / (m : ℂ) ^ (1 / 2 + z)) := by
  simpa only [MulChar.star_apply, RCLike.star_def] using summable_logDerivative_terms (star χ) hz

lemma character_series_projector (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (s z : ℂ) (n m : ℕ) :
    (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N,
      ((mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 + s)) *
      ((mangoldt m : ℂ) * conj (χ m) / (m : ℂ) ^ (1 / 2 + z)) =
        arithmeticExpansionTerm N n m s z := by
  have hfactor : (2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N,
      ((mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 + s)) *
      ((mangoldt m : ℂ) * conj (χ m) / (m : ℂ) ^ (1 / 2 + z)) =
      ((mangoldt n : ℂ) * mangoldt m / ((n : ℂ) ^ (1 / 2 + s) * (m : ℂ) ^ (1 / 2 + z))) *
        ((2 / (N.totient : ℂ)) * ∑ χ ∈ oddCharacters N, χ n * conj (χ m)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  rw [hfactor, lemma_3_1_odd_orthogonality N hN hN4]
  by_cases hn : n = 0
  · subst n
    simp [arithmeticExpansionTerm, mangoldt]
  by_cases hm : m = 0
  · subst m
    simp [arithmeticExpansionTerm, mangoldt]
  simp only [arithmeticExpansionTerm, Nat.pos_of_ne_zero hn, Nat.pos_of_ne_zero hm,
    true_and]
  split_ifs <;> simp_all

lemma characterKernel_dirichlet_expansion (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (s z : ℂ) (hs : 1 / 2 < s.re) (hz : 1 / 2 < z.re) :
    Summable (fun p : ℕ × ℕ => ‖arithmeticExpansionTerm N p.1 p.2 s z‖) ∧
    characterKernel N s z = ∑' p : ℕ × ℕ, arithmeticExpansionTerm N p.1 p.2 s z := by
  let f : Character N → ℕ → ℂ := fun χ n =>
    (mangoldt n : ℂ) * χ n / (n : ℂ) ^ (1 / 2 + s)
  let g : Character N → ℕ → ℂ := fun χ m =>
    (mangoldt m : ℂ) * conj (χ m) / (m : ℂ) ^ (1 / 2 + z)
  have hf (χ : Character N) : Summable (f χ) := summable_logDerivative_terms χ hs
  have hg (χ : Character N) : Summable (g χ) := summable_conjugate_logDerivative_terms χ hz
  have hfg (χ : Character N) : Summable (fun p : ℕ × ℕ => f χ p.1 * g χ p.2) :=
    summable_mul_of_summable_norm (hf χ).norm (hg χ).norm
  have hsum : Summable (fun p : ℕ × ℕ => ∑ χ ∈ oddCharacters N, f χ p.1 * g χ p.2) :=
    summable_sum (fun χ _ => hfg χ)
  have hpoint (p : ℕ × ℕ) :
      (2 / (N.totient : ℂ)) * (∑ χ ∈ oddCharacters N, f χ p.1 * g χ p.2) =
        arithmeticExpansionTerm N p.1 p.2 s z := character_series_projector N hN hN4 s z p.1 p.2
  constructor
  · exact ((hsum.mul_left (2 / (N.totient : ℂ))).congr hpoint).norm
  · calc
      characterKernel N s z = (2 / (N.totient : ℂ)) *
          ∑ χ ∈ oddCharacters N, (∑' n, f χ n) * (∑' m, g χ m) := by
        unfold characterKernel
        congr 1
        apply Finset.sum_congr rfl
        intro χ _
        rw [logDerivative_eq_neg_tsum χ hs, conjugate_logDerivative_eq_neg_tsum χ hz, neg_mul_neg]
      _ = (2 / (N.totient : ℂ)) *
          ∑ χ ∈ oddCharacters N, ∑' p : ℕ × ℕ, f χ p.1 * g χ p.2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro χ _
        exact tsum_mul_tsum_of_summable_norm (hf χ).norm (hg χ).norm
      _ = ∑' p : ℕ × ℕ, (2 / (N.totient : ℂ)) *
          (∑ χ ∈ oddCharacters N, f χ p.1 * g χ p.2) := by
        rw [hsum.tsum_mul_left, Summable.tsum_finsetSum (fun χ _ => hfg χ)]
      _ = _ := tsum_congr hpoint

end ConditionalGoldbach
