import ConditionalGoldbach.Proofs.WideWeight

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma experiment_prime_pair_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (he : p+q=experimentN) : p≠q := by
  intro hh
  have hpv : p=15015 := by norm_num [experimentN] at he; omega
  have hn : ¬Nat.Prime 15015 := by norm_num
  exact hn (hpv ▸ hp)

lemma experiment_prime_pair_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (he : p+q=experimentN) : Nat.Coprime (p*q) experimentN := by
  have hneq := experiment_prime_pair_ne hp hq he
  have hc (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (he : p+q=experimentN) (hn : p≠q) :
      Nat.Coprime p experimentN := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    rw [← he] at hd
    have hpd : p∣q := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hd
    exact hn ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpd)
  exact (hc p q hp hq he hneq).mul_left (hc q p hq hp (by omega) hneq.symm)

def orderedWidePrimeMass : ℝ := ∑ p ∈ Finset.range (experimentN+1),
  if p.Prime ∧ (experimentN-p).Prime then wideCutoff p^2 else 0

def unorderedWidePrimeMass : ℝ := ∑ p ∈ Finset.range (experimentN+1),
  if p.Prime ∧ (experimentN-p).Prime ∧ p≤experimentN-p then wideCutoff p^2 else 0

lemma orderedWidePrimeMass_eq_twice : orderedWidePrimeMass=2*unorderedWidePrimeMass := by
  let S := (Finset.range (experimentN+1)).filter (fun p => p.Prime ∧ (experimentN-p).Prime)
  have hswap : (∑ p ∈ S.filter (fun p => ¬p≤experimentN-p), wideCutoff p^2)=
      ∑ p ∈ S.filter (fun p => p≤experimentN-p), wideCutoff p^2 := by
    apply Finset.sum_bij (fun p _ => experimentN-p)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hS,hgt⟩
      rcases Finset.mem_filter.mp hS with ⟨hr,hp,hq⟩
      have hn : p≤experimentN := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hr
      have hrev : experimentN-(experimentN-p)=p := Nat.sub_sub_self hn
      simp only [Finset.mem_filter,S,Finset.mem_range,Nat.lt_succ_iff,hrev]
      exact ⟨⟨Nat.sub_le _ _,hq,hp⟩,by omega⟩
    · intro p hp q hq he
      have hpN : p≤experimentN := by
        have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        simpa only [Finset.mem_range,Nat.lt_succ_iff] using hh
      have hqN : q≤experimentN := by
        have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
        simpa only [Finset.mem_range,Nat.lt_succ_iff] using hh
      omega
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hS,hle⟩
      rcases Finset.mem_filter.mp hS with ⟨hr,hp,hq⟩
      have hn : p≤experimentN := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hr
      have hneq := experiment_prime_pair_ne hp hq (Nat.add_sub_of_le hn)
      have hrev : experimentN-(experimentN-p)=p := Nat.sub_sub_self hn
      refine ⟨experimentN-p,?_,hrev⟩
      simp only [Finset.mem_filter,S,Finset.mem_range,Nat.lt_succ_iff,hrev]
      exact ⟨⟨Nat.sub_le _ _,hq,hp⟩,by omega⟩
    · intro p hp
      have hpN : p≤experimentN := by
        have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        simpa only [Finset.mem_range,Nat.lt_succ_iff] using hh
      rw [Nat.cast_sub hpN]
      rw [← wideCutoff_reflection]
  have hs := Finset.sum_filter_add_sum_filter_not S (fun p => p≤experimentN-p) (fun p => wideCutoff p^2)
  rw [hswap] at hs
  have he : orderedWidePrimeMass=∑ p ∈ S, wideCutoff p^2 := by simp [orderedWidePrimeMass,S,Finset.sum_filter]
  have hl : unorderedWidePrimeMass=∑ p ∈ S.filter (fun p => p≤experimentN-p), wideCutoff p^2 := by
    simp only [unorderedWidePrimeMass,S,Finset.filter_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [and_assoc]
  rw [he,hl]
  linarith

lemma unorderedWidePrimeMass_add_edge : unorderedWidePrimeMass+edgeCorrection=(unorderedPrimePairs:ℝ) := by
  let pred := fun p : ℕ => p.Prime ∧ (experimentN-p).Prime ∧ p≤experimentN-p
  have he : edgeCorrection=∑ p ∈ Finset.range (experimentN+1), if pred p then 1-wideCutoff p^2 else 0 := by
    unfold edgeCorrection
    apply Finset.sum_subset
    · intro p hp
      simp only [Finset.mem_range,experimentN] at hp ⊢
      omega
    · intro p hp hout
      have hge : 1000≤p := by simpa only [Finset.mem_range,not_lt] using hout
      by_cases hh : pred p
      · have hbound : (p:ℝ)∈Set.Icc (1000:ℝ) (experimentN-1000) := by
          have hpq := hh.2.2
          constructor
          · exact_mod_cast hge
          · have : p≤29030 := by norm_num [experimentN] at hpq; omega
            norm_num [experimentN]
            exact_mod_cast this
        rw [ite_eq_left hh,wideCutoff_plateau p hbound]
        norm_num
      · exact ite_eq_right hh
  have hc : (unorderedPrimePairs:ℝ)=∑ p ∈ Finset.range (experimentN+1), if pred p then (1:ℝ) else 0 := by
    unfold unorderedPrimePairs
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    push_cast
    rfl
  rw [he,hc]
  unfold unorderedWidePrimeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  change (if pred p then _ else _)+(if pred p then _ else _)=(if pred p then _ else _)
  split_ifs <;> ring

end ConditionalGoldbach
