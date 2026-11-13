import LiLiuGoldbach.Proofs.GammaDerivativeLimit
import LiLiuGoldbach.Proofs.GammaResolventBounds

/-! The absolutely convergent digamma difference series, derived from Euler's Gamma limit. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Filter
namespace LiLiuGoldbach16

lemma Gamma_logDeriv_difference_hasSum {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    HasSum (fun n : ℕ => 1/(v+(n:ℂ))-1/(u+(n:ℂ)))
      (logDeriv Gamma u-logDeriv Gamma v) := by
  have hs := (gamma_resolvent_summable_norm hu hv).of_norm
  have hlim := (GammaSeq_logDeriv_tendsto hu).sub (GammaSeq_logDeriv_tendsto hv)
  have he : ∀ᶠ n : ℕ in atTop,
      logDeriv (fun z => GammaSeq z n) u-logDeriv (fun z => GammaSeq z n) v =
        ∑ j ∈ Finset.range (n+1), (1/(v+(j:ℂ))-1/(u+(j:ℂ))) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [GammaSeq_logDeriv hu hn,GammaSeq_logDeriv hv hn,Finset.sum_sub_distrib]
    ring
  have hsum := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique (hlim.congr' he) hsum
  simpa only [heq] using hs.hasSum

lemma Gamma_logDeriv_difference {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    logDeriv Gamma u-logDeriv Gamma v =
      ∑' n : ℕ, (1/(v+(n:ℂ))-1/(u+(n:ℂ))) :=
  (Gamma_logDeriv_difference_hasSum hu hv).tsum_eq.symm

lemma Gamma_logDeriv_difference_norm_le {u v : ℂ}
    (hu : 1/2 ≤ u.re) (hv : 1/2 ≤ v.re) :
    ‖logDeriv Gamma u-logDeriv Gamma v‖ ≤ 8*‖u-v‖ := by
  have hu0 : 0 < u.re := lt_of_lt_of_le (by norm_num) hu
  have hv0 : 0 < v.re := lt_of_lt_of_le (by norm_num) hv
  have hs := Gamma_logDeriv_difference_hasSum hu0 hv0
  apply le_of_tendsto hs.tendsto_sum_nat.norm
  apply Filter.Eventually.of_forall
  intro n
  calc
    ‖∑ j ∈ Finset.range n, (1/(v+(j:ℂ))-1/(u+(j:ℂ)))‖ ≤
        ∑ j ∈ Finset.range n, ‖1/(v+(j:ℂ))-1/(u+(j:ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, (‖u-v‖/(1/2:ℝ)^2)*(1/((j:ℝ)+1)^2) :=
      Finset.sum_le_sum (fun j _ => gamma_resolvent_norm_bound u v (1/2) (by norm_num) (by norm_num) hu hv j)
    _ = (‖u-v‖/(1/2:ℝ)^2)*(∑ j ∈ Finset.range n, 1/((j:ℝ)+1)^2) := by rw [Finset.mul_sum]
    _ ≤ (‖u-v‖/(1/2:ℝ)^2)*2 := by
      gcongr
      exact (sum_one_div_nat_add_one_sq_le n).trans (sub_le_self _ (by positivity))
    _ = _ := by ring

end LiLiuGoldbach16
