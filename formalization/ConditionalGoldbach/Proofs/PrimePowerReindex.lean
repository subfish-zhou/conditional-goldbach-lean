module

public import ConditionalGoldbach.Proofs.PrimePowers
public import Mathlib.Data.Nat.Prime.Int

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

lemma prime_power_parameter_bounds {p k : ℕ} (hp : p.Prime) (hk : 0<k) :
    p≤p^k ∧ k≤p^k := by
  constructor
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hh : 1≤p^j := one_le_pow₀ hp.one_lt.le
    rw [pow_succ]
    nlinarith
  · induction k with
    | zero => simp
    | succ k ih =>
      have ih' : k≤p^k := by
        by_cases hk0 : k=0
        · simp [hk0]
        · exact ih (Nat.pos_of_ne_zero hk0)
      have hh : 1≤p^k := one_le_pow₀ hp.one_lt.le
      rw [pow_succ]
      have := hp.two_le
      nlinarith

def primePowerIndex (N : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.range (N+1))×ˢ(Finset.range (N+1))).filter
    (fun z => z.1.Prime ∧ 0<z.2 ∧ z.1^z.2≤N)

lemma primePowerIndex_image (N : ℕ) :
    (primePowerIndex N).image (fun z => z.1^z.2) = (Finset.range (N+1)).filter IsPrimePow := by
  ext n
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨p,k⟩,hz,rfl⟩
    have hz' := (Finset.mem_filter.mp hz).2
    exact ⟨hz'.2.2,(isPrimePow_nat_iff _).mpr ⟨p,k,hz'.1,hz'.2.1,rfl⟩⟩
  · rintro ⟨hn,hpow⟩
    obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hpow
    have hh := prime_power_parameter_bounds hp hk
    refine ⟨(p,k),?_,rfl⟩
    simp only [primePowerIndex,Finset.mem_filter,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
    exact ⟨⟨hh.1.trans hn,hh.2.trans hn⟩,hp,hk,hn⟩

lemma primePowerIndex_injective (N : ℕ) :
    Set.InjOn (fun z : ℕ×ℕ => z.1^z.2) (primePowerIndex N) := by
  intro x hx y hy he
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  obtain ⟨hp,hk⟩ := hx'.1.pow_inj' hy'.1 hx'.2.1.ne' hy'.2.1.ne' he
  exact Prod.ext hp hk

lemma mangoldt_log_ratio_prime_power {p k : ℕ} (hp : p.Prime) (hk : 0<k) :
    mangoldt (p^k)/Real.log ((p^k:ℕ):ℝ)=(k:ℝ)⁻¹ := by
  change ArithmeticFunction.vonMangoldt (p^k)/Real.log ((p^k:ℕ):ℝ)=_
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',ArithmeticFunction.vonMangoldt_apply_prime hp,
    Nat.cast_pow,Real.log_pow]
  have hlog : Real.log (p:ℝ)≠0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  field_simp

lemma sum_mangoldt_log_reindex (N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N+1), mangoldt n/Real.log n*F n) =
      ∑ p ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+1),
        if p.Prime ∧ 0<k ∧ p^k≤N then F (p^k)/(k:ℝ) else 0 := by
  have hfilter : (∑ n ∈ Finset.range (N+1), mangoldt n/Real.log n*F n) =
      ∑ n ∈ (Finset.range (N+1)).filter IsPrimePow, mangoldt n/Real.log n*F n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : IsPrimePow n
    · simp [hp]
    · have hz : mangoldt n=0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp
      simp [hp,hz]
  rw [hfilter,← primePowerIndex_image N,Finset.sum_image (primePowerIndex_injective N)]
  calc
    _ = ∑ z ∈ primePowerIndex N, F (z.1^z.2)/(z.2:ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hh := (Finset.mem_filter.mp hz).2
      rw [mangoldt_log_ratio_prime_power hh.1 hh.2.1]
      ring
    _ = _ := by
      unfold primePowerIndex
      rw [Finset.sum_filter,Finset.sum_product]

end ConditionalGoldbach
