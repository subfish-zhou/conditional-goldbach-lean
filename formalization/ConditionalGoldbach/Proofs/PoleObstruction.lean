module

public import ConditionalGoldbach.Proofs.PoleLowerBound
public import ConditionalGoldbach.Proofs.PoleSpectralObstruction

/-! The paper's fixed-modulus obstruction, including its sharp leading constant. -/
public section

set_option autoImplicit false
noncomputable section
open scoped Topology
open Set Filter
namespace ConditionalGoldbach

theorem proposition_A_4 (N : ℕ) [NeZero N] (hN : Even N) (hN4 : 4 ≤ N)
    (hGRH : GRH N) (γ : ℝ)
    (hzero : ∃ χ ∈ oddCharacters N, χ.LFunction (line (1 / 2) γ) = 0) :
    0 < poleCoefficient N γ ∧
    (∀ ε : ℝ, 0 < ε → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c < c₀ →
      ∀ ha : alpha N c < beta,
        2 * poleCoefficient N γ * Real.log N / (1 + γ ^ 2) - ε ≤ c * ‖residualOperator ha N‖) ∧
    (∃ z c₀ : ℝ, 0 < z ∧ 0 < c₀ ∧ c₀ ≤ Real.log N / 24 ∧
      ∀ c : ℝ, 0 < c → c < c₀ → ∀ ha : alpha N c < beta,
        z / c ≤ ‖residualOperator ha N‖ ∧ ¬SpectralR N (alpha N c) ha ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → SpectralZeroFree N (alpha N c) ha η →
          η ≤ spectralScale N ^ 2 * c ^ 2 / (3 * z ^ 2)) := by
  have hC := poleCoefficient_pos γ hzero
  have hlim := residualOperator_pole_liminf N hN hN4 hGRH γ
  refine ⟨hC,hlim,?_⟩
  let A : ℝ := 2*poleCoefficient N γ*Real.log N/(1+γ^2)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨c₀,hc₀,hbound⟩ := hlim (A/2) (by positivity)
  have hlower : ∀c : ℝ, 0<c → c<c₀ → ∀ha : alpha N c<beta,
      (A/2)/c ≤ ‖residualOperator ha N‖ := by
    intro c hc hcsmall ha
    apply (div_le_iff₀ hc).mpr
    have hh := hbound c hc hcsmall ha
    change A-A/2 ≤ c*‖residualOperator ha N‖ at hh
    nlinarith
  obtain ⟨c₁,hc₁,hc₁small,hobs⟩ := pole_spectral_obstruction N hN4 hGRH (A/2) c₀
    (by positivity) hc₀ hlower
  exact ⟨A/2,c₁,by positivity,hc₁,hc₁small,hobs⟩

end ConditionalGoldbach
