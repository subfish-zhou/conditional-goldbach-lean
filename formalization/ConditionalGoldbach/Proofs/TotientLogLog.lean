import ConditionalGoldbach.Proofs.ZetaGrowth
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-! The elementary large-prime split upgrading Mertens' product bound to N/φ(N). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
open MathlibNt.SieveTheory.MertensTheorem

lemma primeFactors_card_log_bound (N : ℕ) (hN : 0 < N) :
    (N.primeFactors.card : ℝ)*Real.log 2 ≤ Real.log N := by
  have hp : 2^N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p := by
    calc
      _ = ∏ p ∈ N.primeFactors, 2 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hle := hp.trans (Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N))
  have hr := Real.log_le_log (show (0 : ℝ)<2^N.primeFactors.card by positivity)
    (show (2 : ℝ)^N.primeFactors.card ≤ N by exact_mod_cast hle)
  simpa only [Real.log_pow] using hr

lemma prime_ratio_eq_inv (p : ℕ) (hp : p.Prime) :
    (p : ℝ)/(p-1) = (1-1/(p : ℝ))⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  field_simp

lemma prime_ratio_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ (p : ℝ)/(p-1) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply div_nonneg (by positivity)
  linarith

lemma prime_ratio_ge_one (p : ℕ) (hp : p.Prime) : 1 ≤ (p : ℝ)/(p-1) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply (le_div_iff₀ (by linarith)).2
  linarith

lemma small_prime_ratio_product (N M : ℕ) :
    (∏ p ∈ N.primeFactors.filter (fun p => p ≤ M), (p : ℝ)/(p-1)) ≤ (primeProduct M)⁻¹ := by
  let S := (Finset.range (M+1)).filter Nat.Prime
  have hsub : N.primeFactors.filter (fun p => p ≤ M) ⊆ S := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hpM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_of_mem_primeFactors hp⟩
  have hb : (∏ p ∈ N.primeFactors.filter (fun p => p ≤ M), (p : ℝ)/(p-1)) ≤
      ∏ p ∈ S, (p : ℝ)/(p-1) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p hp => prime_ratio_nonneg p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
    intro p hp hnot
    exact prime_ratio_ge_one p (Finset.mem_filter.mp hp).2
  refine hb.trans_eq ?_
  rw [primeProduct, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact prime_ratio_eq_inv p (Finset.mem_filter.mp hp).2

lemma large_prime_ratio_product (N M : ℕ) (hN : 0 < N) (hM : 1 ≤ M)
    (hlog : Real.log N ≤ M) :
    (∏ p ∈ N.primeFactors.filter (fun p => ¬p ≤ M), (p : ℝ)/(p-1)) ≤
      Real.exp (2/Real.log 2) := by
  let T := N.primeFactors.filter (fun p => ¬p ≤ M)
  have hM0 : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcard : (T.card : ℝ)*Real.log 2 ≤ M := by
    have hc : T.card ≤ N.primeFactors.card := Finset.card_filter_le _ _
    have hcR : (T.card : ℝ) ≤ N.primeFactors.card := by exact_mod_cast hc
    exact ((mul_le_mul_of_nonneg_right hcR hlog2.le).trans (primeFactors_card_log_bound N hN)).trans hlog
  have hb (p : ℕ) (hp : p ∈ T) : (p : ℝ)/(p-1) ≤ Real.exp (2/(M : ℝ)) := by
    have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hpM : (M : ℝ) ≤ p := by exact_mod_cast (show M ≤ p by have := (Finset.mem_filter.mp hp).2; omega)
    have hsmall : 1/((p : ℝ)-1) ≤ 2/(M : ℝ) := by
      apply (div_le_div_iff₀ (by linarith) hM0).2
      nlinarith
    calc
      _ = 1+1/((p : ℝ)-1) := by
        have hn : (p : ℝ)-1 ≠ 0 := by linarith
        field_simp
        <;> ring
      _ ≤ 1+2/(M : ℝ) := by linarith
      _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (2/(M : ℝ))
  calc
    _ ≤ ∏ p ∈ T, Real.exp (2/(M : ℝ)) := by
      exact Finset.prod_le_prod₀ (fun p hp => prime_ratio_nonneg p
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)) hb
    _ = Real.exp (∑ p ∈ T, 2/(M : ℝ)) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply (le_div_iff₀ hlog2).2
      rw [show (T.card : ℝ)*(2/M)*Real.log 2 = ((T.card : ℝ)*2*Real.log 2)/M by ring]
      apply (div_le_iff₀ hM0).2
      nlinarith

lemma totient_ratio_loglog_large :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → 3 ≤ Real.log N →
      (N : ℝ)/N.totient ≤ C*Real.log (Real.log N) := by
  obtain ⟨c,hc,hprod⟩ := primeProduct_lower_bound
  let E := Real.exp (2/Real.log 2)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨2*E/c, by positivity, fun N hN hlog => ?_⟩
  let M : ℕ := Nat.ceil (Real.log N)
  have hlog0 : 0 < Real.log N := by linarith
  have hNM : Real.log N ≤ M := Nat.le_ceil _
  have hM3 : 3 ≤ M := by exact_mod_cast (show (3 : ℝ) ≤ M by linarith)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hMup : (M : ℝ) ≤ 2*Real.log N := by
    have hh := Nat.ceil_lt_add_one hlog0.le
    dsimp [M]
    linarith
  have hLL : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hlogs : Real.log M ≤ 2*Real.log (Real.log N) := by
    have hh := Real.log_le_log hM0 hMup
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hlog0.ne'] at hh
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) (show (2 : ℝ)≤Real.log N by linarith)
    linarith
  have hsmall : (∏ p ∈ N.primeFactors.filter (fun p => p ≤ M), (p : ℝ)/(p-1)) ≤ Real.log M/c := by
    apply (small_prime_ratio_product N M).trans
    have hh := one_div_le_one_div_of_le (div_pos hc hlogM) (hprod M hM3)
    simpa only [one_div, inv_div] using hh
  rw [totient_ratio_prod N hN, ← Finset.prod_filter_mul_prod_filter_not
    N.primeFactors (fun p => p ≤ M)]
  calc
    _ ≤ (Real.log M/c)*E := mul_le_mul hsmall
      (large_prime_ratio_product N M hN (by omega) hNM)
      (Finset.prod_nonneg (fun p hp => prime_ratio_nonneg p
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))) (by positivity)
    _ ≤ (2*Real.log (Real.log N)/c)*E :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlogs hc.le) hE.le
    _ = _ := by ring

lemma totient_ratio_loglog_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      (N : ℝ)/N.totient ≤ C*Real.log (Real.log N) := by
  obtain ⟨C,hC,hlarge⟩ := totient_ratio_loglog_large
  let K : ℕ := Nat.ceil (Real.exp 3)+1
  let B : ℝ := ∑ n ∈ Finset.range K, |((n : ℝ)/n.totient)/Real.log (Real.log n)|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C+B+1, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog2 : (1 : ℝ) < Real.log (4 : ℝ) := by
    have he : Real.exp (1 : ℝ) < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr he
  have hlogN : 1 < Real.log N := hlog2.trans_le
    (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hLL : 0 < Real.log (Real.log N) := Real.log_pos hlogN
  by_cases hbig : 3 ≤ Real.log N
  · exact (hlarge N (by omega) hbig).trans (mul_le_mul_of_nonneg_right (by linarith) hLL.le)
  · have hlt : (N : ℝ) < Real.exp 3 := by
      exact (Real.log_lt_iff_lt_exp hN0).mp (lt_of_not_ge hbig)
    have hNK : N < K := by
      have hh := Nat.le_ceil (Real.exp 3)
      have : (N : ℝ) < (Nat.ceil (Real.exp 3) : ℝ) := hlt.trans_le hh
      have : N < Nat.ceil (Real.exp 3) := by exact_mod_cast this
      dsimp [K]
      omega
    have hb : ((N : ℝ)/N.totient)/Real.log (Real.log N) ≤ B := by
      apply (le_abs_self _).trans
      exact Finset.single_le_sum
        (f := fun n : ℕ => |((n : ℝ)/n.totient)/Real.log (Real.log n)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hNK)
    have hh := (div_le_iff₀ hLL).mp hb
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hLL.le)

theorem lemma_4_3_uniform (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Even N → 4 ≤ N →
      (∀ w : ℂ, w.re ∈ Icc lo hi → 1 ≤ |w.im| →
        ‖continuedDensity N w‖ ≤ C * (N : ℝ) / N.totient * (1 + |w.im|)) ∧
      (N : ℝ) / N.totient ≤ C * Real.log (Real.log N) := by
  obtain ⟨C₁,hC₁,h₁⟩ := continuedDensity_uniform_vertical_growth hlo hhi
  obtain ⟨C₂,hC₂,h₂⟩ := totient_ratio_loglog_bound
  refine ⟨C₁+C₂, by positivity, fun N hN hN4 => ⟨?_,?_⟩⟩
  · intro w hw ht
    apply (h₁ N hN hN4 w hw ht).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · apply (h₂ N hN4).trans
    apply mul_le_mul_of_nonneg_right (by linarith)
    have h4 : (1 : ℝ) < Real.log 4 := by
      apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
      exact lt_trans Real.exp_one_lt_d9 (by norm_num)
    apply Real.log_nonneg
    exact h4.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN4))

end ConditionalGoldbach
