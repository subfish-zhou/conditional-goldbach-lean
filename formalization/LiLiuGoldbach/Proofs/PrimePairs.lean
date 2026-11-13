import LiLiuGoldbach.Proofs.Main
import LiLiuGoldbach.Proofs.Asymptotics
import LiLiuGoldbach.Proofs.PrimePowers

/-! The paper's unnumbered prime-pair consequence, combining prime-power removal,
counting inequalities, and the proved conditional asymptotic in Theorem 1.1. -/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace LiLiuGoldbach16

theorem primePair_consequence (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (hGRH : EvenEventually GRH) (hSpectral : HypothesisR ∨ ∃ h, HypothesisS h) :
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      C * singularSeries N * N / Real.log N ^ 2 ≤ (PrimePairCount N : ℝ)) := by
  have hexS : ∃ h, HypothesisS h := by
    rcases hSpectral with hR | hS
    · exact ⟨fun N => Real.log (N : ℝ),
        theorem_1_2_hypothesisR_implies_S hR _ isAdmissible_log⟩
    · exact hS
  obtain ⟨h, hS⟩ := hexS
  obtain ⟨K, _, hK⟩ := theorem_1_1 φ hφ
  have hasym := (hK h hGRH hS).2 (1 / 2) (by norm_num)
  have hm : 0 < weightMass φ := weightMass_pos hφ
  have hε : 0 < weightMass φ * C2 / 2 := div_pos (mul_pos hm C2_pos) (by norm_num)
  have hbad := evenEventually_of_eventually
    ((tendsto_order.1 tendsto_prime_power_error).2 (weightMass φ * C2 / 2) hε)
  refine ⟨weightMass φ / 4, by positivity, ?_⟩
  obtain ⟨k, hk⟩ := hasym.and (hbad.and evenEventually_large)
  refine ⟨k, fun N hNk he => ?_⟩
  rcases hk N hNk he with ⟨happrox, hbadsmall, hlarge⟩
  rcases large_parameters hlarge with ⟨hN4, hlog, _⟩
  have hN : 0 < N := by omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < weightMass φ * singularSeries N := mul_pos hm (singularSeries_pos N)
  change |goldbach N φ / (weightMass φ * singularSeries N) - 1| < 1 / 2 at happrox
  have hratio : (1 / 2 : ℝ) < goldbach N φ / (weightMass φ * singularSeries N) := by
    linarith [(abs_lt.1 happrox).1]
  have hgold := (lt_div_iff₀ hden).1 hratio
  have hbadupper : badGoldbachMass N φ ≤ weightMass φ * singularSeries N / 4 := by
    have hbase := mul_le_mul_of_nonneg_left (singularSeries_uniform_lower N) hm.le
    calc
      _ ≤ 4 * Real.log N ^ 2 / Real.sqrt N := badGoldbachMass_le_sqrt N hN φ hφ
      _ ≤ weightMass φ * C2 / 2 := hbadsmall.le
      _ ≤ weightMass φ * singularSeries N / 4 := by linarith
  have hcount := goldbach_le_badGoldbachMass_add_primePairCount N hN φ hφ
  have hcountprod : (weightMass φ / 4) * singularSeries N ≤
      (Real.log N ^ 2 / N) * (PrimePairCount N : ℝ) := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hlog)).2
  calc
    _ ≤ ((Real.log N ^ 2 / N) * (PrimePairCount N : ℝ)) * N :=
      mul_le_mul_of_nonneg_right hcountprod hNR.le
    _ = (PrimePairCount N : ℝ) * Real.log N ^ 2 := by
      field_simp

end LiLiuGoldbach16
