import ConditionalGoldbach.Proofs.PrimePowerReindex

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma sum_mangoldt_log_double_reindex (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range (N+1), ∑ m ∈ Finset.range (N+1),
      (mangoldt n/Real.log n)*(mangoldt m/Real.log m)*F n m) =
    ∑ p ∈ Finset.range (N+1), ∑ q ∈ Finset.range (N+1),
      ∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1),
      if (p.Prime ∧ 0<k ∧ p^k≤N) ∧ (q.Prime ∧ 0<l ∧ q^l≤N)
      then F (p^k) (q^l)/(k*l:ℕ) else 0 := by
  calc
    _ = ∑ n ∈ Finset.range (N+1), (mangoldt n/Real.log n)*
        (∑ m ∈ Finset.range (N+1), (mangoldt m/Real.log m)*F n m) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ = ∑ p ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+1),
        if p.Prime ∧ 0<k ∧ p^k≤N then
          (∑ m ∈ Finset.range (N+1), (mangoldt m/Real.log m)*F (p^k) m)/(k:ℝ) else 0 :=
      sum_mangoldt_log_reindex N _
    _ = ∑ p ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+1),
        ∑ q ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1),
          if (p.Prime ∧ 0<k ∧ p^k≤N) ∧ (q.Prime ∧ 0<l ∧ q^l≤N)
          then F (p^k) (q^l)/(k*l:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      rw [sum_mangoldt_log_reindex N (F (p^k))]
      by_cases hpk : p.Prime ∧ 0<k ∧ p^k≤N
      · simp only [hpk,ite_true,true_and,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro l hl
        split_ifs
        · push_cast
          ring
        · simp
      · simp [hpk]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]

lemma primePower_coprime {p q k l N : ℕ} (hk : 0<k) (hl : 0<l) :
    Nat.Coprime (p^k*q^l) N ↔ Nat.Coprime (p*q) N := by
  simp only [Nat.coprime_mul_iff_left,Nat.coprime_pow_left_iff hk,Nat.coprime_pow_left_iff hl]

lemma sum_mangoldt_log_add_reindex (N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N+1), ∑ m ∈ Finset.range (N+1),
      (mangoldt n/Real.log n)*(mangoldt m/Real.log m)*
        (if n+m=N ∧ Nat.Coprime (n*m) N then F n else 0)) =
    ∑ p ∈ Finset.range (N+1), ∑ q ∈ Finset.range (N+1),
      ∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1),
        if p.Prime ∧ q.Prime ∧ 0<k ∧ 0<l ∧ p^k+q^l=N ∧ Nat.Coprime (p*q) N
        then F (p^k)/(k*l:ℕ) else 0 := by
  rw [sum_mangoldt_log_double_reindex]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hP : p.Prime
  · by_cases hQ : q.Prime
    · by_cases hK : 0<k
      · by_cases hL : 0<l
        · simp only [primePower_coprime hK hL]
          by_cases he : p^k+q^l=N
          · have hpN : p^k≤N := by omega
            have hqN : q^l≤N := by omega
            simp only [hP,hQ,hK,hL,he,hpN,hqN,and_self,true_and,ite_true]
            split_ifs <;> simp
          · simp [he,hP,hQ,hK,hL]
        · simp [hL]
      · simp [hK]
    · simp [hQ]
  · simp [hP]

end ConditionalGoldbach
