module

public import ConditionalGoldbach.Proofs.VariableQuadratic

/-! The spectral consequences of the genuine pole lower bound, with the original constants. -/
public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma pole_spectral_obstruction (N : ℕ) [NeZero N] (hN4 : 4 ≤ N) (hGRH : GRH N)
    (z c₀ : ℝ) (hz : 0 < z) (hc₀ : 0 < c₀)
    (hlower : ∀ c : ℝ, 0 < c → c < c₀ → ∀ ha : alpha N c < beta,
      z/c ≤ ‖residualOperator ha N‖) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ Real.log N / 24 ∧
      ∀ c : ℝ, 0 < c → c < c₁ → ∀ ha : alpha N c < beta,
        z/c ≤ ‖residualOperator ha N‖ ∧ ¬SpectralR N (alpha N c) ha ∧
        ∀ η : ℝ, 0 < η → η ≤ 1/4 → SpectralZeroFree N (alpha N c) ha η →
          η ≤ spectralScale N^2*c^2/(3*z^2) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hscale : 0 < spectralScale N := spectralScale_pos N
    (by exact_mod_cast (show 0<N by omega)) (singularSeries_pos N) hlog
  let c₁ := min c₀ (min (Real.log N/24) (z/(spectralScale N+1)))
  have hc₁ : 0 < c₁ := lt_min hc₀ (lt_min (by positivity) (by positivity))
  refine ⟨c₁,hc₁,(min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro c hc hcc ha
  have hcc₀ : c < c₀ := hcc.trans_le (min_le_left _ _)
  have hcz : c < z/(spectralScale N+1) :=
    hcc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbound := hlower c hc hcc₀ ha
  have hdict := variable_spectral_dictionary (alpha N c) (alpha_pos_at N hN4 c hc) N hN4 hGRH ha
  have hlarge : spectralScale N < z/c := by
    apply (lt_div_iff₀ hc).mpr
    have hh := (lt_div_iff₀ (by positivity : 0 < spectralScale N+1)).mp hcz
    nlinarith
  refine ⟨hbound,fun hR => (not_lt_of_ge (hbound.trans (hdict.1.mp hR))) hlarge,?_⟩
  intro η hη hη4 hzero
  have hη1 : 0 < 1-η := by linarith
  have hprod : 0 < η*(1-η) := mul_pos hη hη1
  have hden : 0 < 2*Real.sqrt (η*(1-η)) := by positivity
  have hupper := (hdict.2 η hη (by linarith)).mp hzero
  have hmain : z*(2*Real.sqrt (η*(1-η))) ≤ spectralScale N*c :=
    (div_le_div_iff₀ hc hden).mp (hbound.trans hupper)
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ z*(2*Real.sqrt (η*(1-η)))) hmain
  have hsqrt := Real.sq_sqrt hprod.le
  have hsquared : 4*z^2*(η*(1-η)) ≤ spectralScale N^2*c^2 := by
    calc
      _ = (z*(2*Real.sqrt (η*(1-η))))*(z*(2*Real.sqrt (η*(1-η)))) := by
        nlinarith [mul_nonneg (sq_nonneg z) (sq_nonneg (Real.sqrt (η*(1-η))))]
      _ ≤ (spectralScale N*c)*(spectralScale N*c) := hsq
      _ = _ := by ring
  have hηsmall : 3*z^2*η ≤ 4*z^2*(η*(1-η)) := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ z^2*η) (show 0 ≤ 1-4*η by linarith)]
  apply (le_div_iff₀ (by positivity : 0 < 3*z^2)).mpr
  nlinarith

end ConditionalGoldbach
