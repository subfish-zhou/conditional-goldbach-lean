module

public import ConditionalGoldbach.Proofs.WidePrimePairs
public import ConditionalGoldbach.Proofs.PrimePowerDouble

public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
open Set
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma wideWeight_product_all (u : ℝ) :
    wideWeight u*wideWeight (1-u)=wideCutoff (experimentN*u)^2/
      (Real.log (experimentN*u)*Real.log (experimentN*(1-u))) := by
  by_cases hu : u∈Ioo (16/experimentN:ℝ) (1-16/experimentN:ℝ)
  · exact wideWeight_product u hu
  · have hw : wideWeight u=0 := by
      by_contra hn
      exact hu (wideWeight_support hn)
    have hc : wideCutoff (experimentN*u)=0 := by
      simp only [mem_Ioo,not_and_or,not_lt] at hu
      rcases hu with hu|hu
      · apply wideCutoff_zero_left
        norm_num [experimentN] at hu ⊢
        linarith
      · apply wideCutoff_zero_right
        norm_num [experimentN] at hu ⊢
        linarith
    rw [hw,hc]
    simp

lemma wideWeight_discrete_product {n m : ℕ} (he : n+m=experimentN) :
    wideWeight (n/experimentN)*wideWeight (m/experimentN)=
      wideCutoff n^2/(Real.log n*Real.log m) := by
  have he' : (n:ℝ)+(m:ℝ)=experimentN := by exact_mod_cast he
  have hm : (m:ℝ)/experimentN=1-(n:ℝ)/experimentN := by
    norm_num [experimentN] at he' ⊢
    linarith
  rw [hm,wideWeight_product_all]
  have hn : (experimentN:ℝ)*((n:ℝ)/experimentN)=n := by field_simp
  have hm' : (experimentN:ℝ)*(1-(n:ℝ)/experimentN)=m := by rw [← hm]; field_simp
  rw [hn,hm']

lemma wideCorrelation_double_sum : (experimentN:ℝ)*wideCorrelation=
    ∑ n∈Finset.range (experimentN+1), ∑ m∈Finset.range (experimentN+1),
      (mangoldt n/Real.log n)*(mangoldt m/Real.log m)*
        (if n+m=experimentN ∧ Nat.Coprime (n*m) experimentN then wideCutoff n^2 else 0) := by
  unfold wideCorrelation goldbach
  rw [← mul_assoc,mul_inv_cancel₀ (by norm_num [experimentN] : (experimentN:ℝ)≠0),one_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n≤experimentN := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
  rw [Finset.sum_eq_single (experimentN-n)]
  · have he : n+(experimentN-n)=experimentN := Nat.add_sub_of_le hnN
    by_cases h0 : 0<n
    · by_cases hN : n<experimentN
      · by_cases hc : Nat.Coprime (n*(experimentN-n)) experimentN
        · simp only [h0,hN,he,true_and]
          rw [mul_assoc (mangoldt n*mangoldt (experimentN-n)),wideWeight_discrete_product he]
          split_ifs; ring
        · simp [hc]
      · have hnE : n=experimentN := by omega
        subst n
        simp [mangoldt]
    · have hn0 : n=0 := by omega
      subst n
      simp [mangoldt]
  · intro m hm hmn
    have he : ¬n+m=experimentN := by omega
    simp [he]
  · intro hnot
    exact False.elim (hnot (by simp only [Finset.mem_range]; omega))

lemma primePower_exponents_split (p q k l : ℕ) :
    (if p.Prime ∧ q.Prime ∧ 0<k ∧ 0<l ∧ p^k+q^l=experimentN ∧ Nat.Coprime (p*q) experimentN
      then wideCutoff (p^k)^2/(k*l:ℕ) else 0) =
    (if p.Prime ∧ q.Prime ∧ 0<k ∧ 0<l ∧ 2 ≤ max k l ∧ p^k+q^l=experimentN ∧ Nat.Coprime (p*q) experimentN
      then wideCutoff (p^k)^2/(k*l:ℕ) else 0)+
    (if k=1 ∧ l=1 ∧ p.Prime ∧ q.Prime ∧ p+q=experimentN ∧ Nat.Coprime (p*q) experimentN
      then wideCutoff p^2 else 0) := by
  by_cases hk : k=1
  · subst k
    by_cases hl : l=1
    · subst l
      simp
    · have he : 0<l → 2 ≤ max 1 l := by omega
      by_cases hL : 0<l
      · simp [hl,hL,he hL]
      · simp [hl,hL]
  · by_cases hK : 0<k
    · have he : 2 ≤ max k l := by omega
      simp [hk,hK,he]
    · simp [hk,hK]

lemma primePower_linear_sum (p q : ℕ) :
    (∑ k∈Finset.range (experimentN+1), ∑ l∈Finset.range (experimentN+1),
      if k=1 ∧ l=1 ∧ p.Prime ∧ q.Prime ∧ p+q=experimentN ∧ Nat.Coprime (p*q) experimentN
        then wideCutoff p^2 else 0) =
    if p.Prime ∧ q.Prime ∧ p+q=experimentN ∧ Nat.Coprime (p*q) experimentN then wideCutoff p^2 else 0 := by
  rw [Finset.sum_eq_single 1]
  · rw [Finset.sum_eq_single 1]
    · simp
    · intro l hl hl1
      simp [hl1]
    · intro hnot
      exact False.elim (hnot (by norm_num [experimentN]))
  · intro k hk hk1
    simp [hk1]
  · intro hnot
    exact False.elim (hnot (by norm_num [experimentN]))

lemma primePower_linear_pair_sum :
    (∑ p∈Finset.range (experimentN+1), ∑ q∈Finset.range (experimentN+1),
      if p.Prime ∧ q.Prime ∧ p+q=experimentN ∧ Nat.Coprime (p*q) experimentN then wideCutoff p^2 else 0) =
    orderedWidePrimeMass := by
  unfold orderedWidePrimeMass
  apply Finset.sum_congr rfl
  intro p hp
  have hpN : p≤experimentN := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hp
  rw [Finset.sum_eq_single (experimentN-p)]
  · by_cases hP : p.Prime
    · by_cases hQ : (experimentN-p).Prime
      · have hc := experiment_prime_pair_coprime hP hQ (Nat.add_sub_of_le hpN)
        simp only [hP,hQ,Nat.add_sub_of_le hpN,true_and,ite_true]
        exact ite_eq_left hc
      · simp [hQ]
    · simp [hP]
  · intro q hq hqp
    have he : ¬p+q=experimentN := by omega
    simp [he]
  · intro hnot
    exact False.elim (hnot (by simp only [Finset.mem_range]; omega))

lemma wideCorrelation_primePower_decomposition :
    (experimentN:ℝ)*wideCorrelation=primePowerCorrection+orderedWidePrimeMass := by
  rw [wideCorrelation_double_sum,sum_mangoldt_log_add_reindex]
  simp only [Nat.cast_pow]
  simp only [primePower_exponents_split,Finset.sum_add_distrib,primePower_linear_sum]
  rw [primePower_linear_pair_sum]
  rfl

theorem proposition_B_1 :
    ContDiff ℝ 6 wideCutoff ∧ (∀ x : ℝ, wideCutoff x = wideCutoff (experimentN - x)) ∧
    (∀ x ∈ Icc (1000 : ℝ) (experimentN - 1000), wideCutoff x = 1) ∧
    (∀ u ∈ Ioo (16 / experimentN : ℝ) (1 - 16 / experimentN : ℝ),
      wideWeight u * wideWeight (1 - u) = wideCutoff (experimentN * u) ^ 2 /
        (Real.log (experimentN * u) * Real.log (experimentN * (1 - u)))) ∧
    (unorderedPrimePairs : ℝ) = (experimentN : ℝ) / 2 * wideCorrelation - primePowerCorrection / 2 + edgeCorrection := by
  refine ⟨wideCutoff_contDiff,wideCutoff_reflection,wideCutoff_plateau,wideWeight_product,?_⟩
  have h := wideCorrelation_primePower_decomposition
  rw [orderedWidePrimeMass_eq_twice] at h
  have he := unorderedWidePrimeMass_add_edge
  norm_num only [experimentN,Nat.cast_ofNat] at h ⊢
  linarith

/-- The exact prime-pair count obtained by the two corrections in Proposition B.1. -/
lemma unorderedPrimePairs_eq_corrected_wideCorrelation :
    (unorderedPrimePairs : ℝ) =
      (experimentN : ℝ) / 2 * wideCorrelation - primePowerCorrection / 2 + edgeCorrection := by
  obtain ⟨_, _, _, _, hCount⟩ := proposition_B_1
  exact hCount

end ConditionalGoldbach
