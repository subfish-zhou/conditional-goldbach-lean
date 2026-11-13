import LiLiuGoldbach.Proofs.CharacterAnalytic

/-! An explicit common entire denominator for the two-variable character kernel. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable conductorNeZero

lemma differentiable_product_two_variables {ι : Type*} (S : Finset ι)
    (f : ι → ℂ × ℂ → ℂ) (hf : ∀ i ∈ S, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun p => ∏ i ∈ S, f i p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (differentiable_const (c := (1 : ℂ)))
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma finite_entire_quotient_sum {ι : Type*} (S : Finset ι)
    (a b : ι → ℂ × ℂ → ℂ) (ha : ∀ i ∈ S, Differentiable ℂ (a i))
    (hb : ∀ i ∈ S, Differentiable ℂ (b i)) :
    ∃ A : ℂ × ℂ → ℂ, Differentiable ℂ A ∧
      ∀ p, (∏ i ∈ S, b i p) ≠ 0 →
        (∑ i ∈ S, a i p / b i p) = A p / (∏ i ∈ S, b i p) := by
  classical
  refine ⟨fun p => ∑ i ∈ S, a i p * ∏ j ∈ S.erase i, b j p, ?_, ?_⟩
  · apply Differentiable.fun_sum
    intro i hi
    exact (ha i hi).mul (differentiable_product_two_variables _ _
      (fun j hj => hb j (Finset.mem_of_mem_erase hj)))
  · intro p hp
    apply (eq_div_iff hp).2
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hbi : b i p ≠ 0 := Finset.prod_ne_zero_iff.mp hp i hi
    rw [← Finset.mul_prod_erase S (fun j => b j p) hi]
    field_simp

lemma odd_character_product_star (N : ℕ) [NeZero N] (f : Character N → ℂ) :
    (∏ χ ∈ oddCharacters N, f (star χ)) = ∏ χ ∈ oddCharacters N, f χ := by
  apply Finset.prod_bij (fun χ _ => star χ)
  · intro χ hχ
    exact (star_mem_oddCharacters χ).2 hχ
  · intro a ha b hb hab
    simpa using congrArg star hab
  · intro χ hχ
    exact ⟨star χ, (star_mem_oddCharacters χ).2 hχ, by simp⟩
  · intro χ _
    rfl

theorem proposition_3_2_joint_meromorphic (N : ℕ) [NeZero N]
    (hN : Even N) (hN4 : 4 ≤ N) :
    let B : ℂ × ℂ → ℂ := fun p => ∏ χ ∈ oddCharacters N,
      χ.LFunction (1 / 2 + p.1) * χ.LFunction (1 / 2 + p.2)
    Differentiable ℂ B ∧ B ≠ 0 ∧
    (∃ A : ℂ × ℂ → ℂ, Differentiable ℂ A ∧
      ∀ p : ℂ × ℂ, B p ≠ 0 → characterKernel N p.1 p.2 = A p / B p) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => characterKernel N p.1 p.2)
      {p | ∀ χ ∈ oddCharacters N,
        χ.LFunction (1 / 2 + p.1) ≠ 0 ∧ χ.LFunction (1 / 2 + p.2) ≠ 0} := by
  classical
  let L : Character N → ℂ → ℂ := fun χ s => χ.LFunction (1 / 2 + s)
  let a : Character N → ℂ × ℂ → ℂ := fun χ p =>
    deriv χ.LFunction (1 / 2 + p.1) * deriv (star χ).LFunction (1 / 2 + p.2)
  let b : Character N → ℂ × ℂ → ℂ := fun χ p => L χ p.1 * L (star χ) p.2
  let B : ℂ × ℂ → ℂ := fun p => ∏ χ ∈ oddCharacters N, L χ p.1 * L χ p.2
  have hL (χ : Character N) (hχ : χ ∈ oddCharacters N) : Differentiable ℂ χ.LFunction :=
    DirichletCharacter.differentiable_LFunction (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2)
  have hfirst : Differentiable ℂ (fun p : ℂ × ℂ => 1 / 2 + p.1) := by fun_prop
  have hsecond : Differentiable ℂ (fun p : ℂ × ℂ => 1 / 2 + p.2) := by fun_prop
  have ha (χ : Character N) (hχ : χ ∈ oddCharacters N) : Differentiable ℂ (a χ) :=
    ((hL χ hχ).deriv.comp hfirst).mul
      ((hL (star χ) ((star_mem_oddCharacters χ).2 hχ)).deriv.comp hsecond)
  have hb (χ : Character N) (hχ : χ ∈ oddCharacters N) : Differentiable ℂ (b χ) :=
    ((hL χ hχ).comp hfirst).mul
      ((hL (star χ) ((star_mem_oddCharacters χ).2 hχ)).comp hsecond)
  have hB : Differentiable ℂ B := differentiable_product_two_variables _ _
    (fun χ hχ => ((hL χ hχ).comp hfirst).mul ((hL χ hχ).comp hsecond))
  have hprod (p : ℂ × ℂ) : (∏ χ ∈ oddCharacters N, b χ p) = B p := by
    dsimp [b, B]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, odd_character_product_star N (fun χ => L χ p.2)]
  have hBne : B ≠ 0 := by
    intro hzero
    have hnz : B (2, 2) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro χ hχ
      apply mul_ne_zero <;>
        exact χ.LFunction_ne_zero_of_one_le_re (Or.inl (odd_character_ne_one χ
          (Finset.mem_filter.mp hχ).2)) (by norm_num)
    exact hnz (congrFun hzero (2, 2))
  obtain ⟨A, hA, hquot⟩ := finite_entire_quotient_sum (oddCharacters N) a b ha hb
  refine ⟨hB, hBne, ⟨fun p => (2 / (N.totient : ℂ)) * A p, hA.const_mul _, ?_⟩, ?_⟩
  · intro p hp
    change characterKernel N p.1 p.2 = (2 / (N.totient : ℂ)) * A p / B p
    rw [characterKernel_eq_star_sum]
    have hs : (∑ χ ∈ oddCharacters N, logDerivative χ p.1 * logDerivative (star χ) p.2) =
        A p / B p := by
      rw [← hprod, ← hquot p (by rwa [hprod])]
      apply Finset.sum_congr rfl
      intro χ hχ
      dsimp [logDerivative, a, b, L]
      ring
    rw [hs]
    ring
  · intro p hp
    apply DifferentiableAt.differentiableWithinAt
    simp_rw [characterKernel_eq_star_sum]
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.fun_sum
    intro χ hχ
    have hχ1 := odd_character_ne_one χ (Finset.mem_filter.mp hχ).2
    have hχstar := odd_character_ne_one (star χ)
      (Finset.mem_filter.mp ((star_mem_oddCharacters χ).2 hχ)).2
    exact ((logDerivative_analyticAt_of_ne_zero χ hχ1 (hp χ hχ).1).differentiableAt.comp p differentiableAt_fst).mul
      ((logDerivative_analyticAt_of_ne_zero (star χ) hχstar
        (hp (star χ) ((star_mem_oddCharacters χ).2 hχ)).2).differentiableAt.comp p differentiableAt_snd)

end LiLiuGoldbach16
