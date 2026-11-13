import ConditionalGoldbach.Proofs.Characters

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma full_character_selector {N : ℕ} [NeZero N] (n m : ℕ) :
    (N.totient:ℂ)⁻¹ * ∑ χ : Character N, χ n*conj (χ m) =
      if Nat.Coprime (n*m) N then (if (n:ZMod N)=m then 1 else 0) else 0 := by
  have hφ : (N.totient:ℂ)≠0 := by exact_mod_cast (NeZero.ne N.totient)
  by_cases hc : Nat.Coprime (n*m) N
  · have hm := (Nat.coprime_mul_iff_left.mp hc).2
    rw [full_character_orthogonality _ _ ((ZMod.isUnit_iff_coprime m N).mpr hm),ite_eq_left hc]
    split_ifs <;> simp [hφ]
  · rw [ite_eq_right hc]
    suffices (∑ χ : Character N, χ n*conj (χ m))=0 by rw [this,mul_zero]
    apply Finset.sum_eq_zero
    intro χ _
    have hh : ¬Nat.Coprime n N ∨ ¬Nat.Coprime m N := by simpa only [Nat.coprime_mul_iff_left,not_and_or] using hc
    rcases hh with hn|hm
    · have hz : χ (n:ZMod N)=0 := MulChar.map_nonunit χ (by simpa [ZMod.isUnit_iff_coprime] using hn)
      simp [hz]
    · have hz : χ (m:ZMod N)=0 := MulChar.map_nonunit χ (by simpa [ZMod.isUnit_iff_coprime] using hm)
      simp [hz]

lemma full_character_quadratic (N : ℕ) [NeZero N] (s : Finset ℕ) (c : ℕ → ℝ) :
    (N.totient:ℝ)⁻¹ * ∑ χ : Character N, ‖∑ n ∈ s, (c n:ℂ)*χ n‖^2 =
      ∑ n ∈ s, ∑ m ∈ s, c n*c m *
        (if Nat.Coprime (n*m) N then (if (n:ZMod N)=m then (1:ℝ) else 0) else 0) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_sum]
  simp_rw [character_sum_norm_sq_complex]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := s),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  calc
    (∑ χ : Character N, (N.totient:ℂ)⁻¹*((c n:ℂ)*c m*(χ n*conj (χ m)))) =
        (c n:ℂ)*c m*((N.totient:ℂ)⁻¹*∑ χ : Character N, χ n*conj (χ m)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by rw [full_character_selector]; split_ifs <;> norm_num

lemma finite_full_projection (N : ℕ) [NeZero N] (c : ℕ → ℝ) (h0 : c 0=0) (hN : c N=0) :
    (N.totient:ℝ)⁻¹ * ∑ χ : Character N, ‖∑ n ∈ Finset.range (N+1), (c n:ℂ)*χ n‖^2 =
      ∑ n ∈ Finset.range (N+1), if Nat.Coprime n N then c n^2 else 0 := by
  rw [full_character_quadratic]
  apply Finset.sum_congr rfl
  intro n hn
  have hnn : n≤N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
  have he (m : ℕ) (hm : m∈Finset.range (N+1)) :
      c n*c m*(if Nat.Coprime (n*m) N then (if (n:ZMod N)=m then (1:ℝ) else 0) else 0)=
        if n=m then (if Nat.Coprime n N then c n^2 else 0) else 0 := by
    by_cases hcn : c n=0
    · simp [hcn]
    by_cases hcm : c m=0
    · by_cases hnm : n=m
      · subst m; exact (hcn hcm).elim
      · simp [hcm,hnm]
    have hn0 : 0<n := Nat.pos_of_ne_zero (by intro hz; subst n; exact hcn h0)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by intro hz; subst m; exact hcm h0)
    have hnN : n<N := lt_of_le_of_ne hnn (by intro hz; subst n; exact hcn hN)
    have hmN : m<N := by
      have hh : m≤N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hm
      exact lt_of_le_of_ne hh (by intro hz; subst m; exact hcm hN)
    simp only [(residue_diagonals (NeZero.pos N) hn0 hnN hm0 hmN).1]
    by_cases hnm : n=m
    · subst m
      simp only [ite_true,Nat.coprime_mul_iff_left,and_self]
      split_ifs <;> simp [pow_two]
    · simp [hnm]
  rw [Finset.sum_congr rfl he,Finset.sum_ite_eq,ite_eq_left hn]

lemma signed_character_energy (N : ℕ) [NeZero N] (v : Character N → ℝ) :
    (∑ χ : Character N, (χ (-1)).re*v χ) = ∑ χ : Character N, v χ - 2*∑ χ ∈ oddCharacters N, v χ := by
  rw [oddCharacters,Finset.sum_filter,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  rcases χ.even_or_odd with he|ho
  · have hnot : χ (-1)≠-1 := he.not_odd
    have hv : χ (-1)=1 := he
    norm_num [hv]
  · have hv : χ (-1)=-1 := ho
    simp [hv]
    ring

end ConditionalGoldbach
