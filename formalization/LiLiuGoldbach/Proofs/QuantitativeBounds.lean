import LiLiuGoldbach.Proofs.CharacterAverage
import LiLiuGoldbach.Proofs.SpectralQuantitative
import LiLiuGoldbach.Proofs.BalanceBounds
import LiLiuGoldbach.Proofs.BalanceLimits

set_option autoImplicit false
noncomputable section
open Set Filter
namespace LiLiuGoldbach16

lemma residualOperator_uniform_hs_bound : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Even N → Real.exp 10<(N:ℝ) → GRH N → ∀ a : ℝ, 0<a → ∀ ha : a<beta,
      IsHilbertSchmidt (residualOperator ha N) ∧
      ‖residualOperator ha N‖≤hsNorm (residualOperator ha N) ∧
      hsNorm (residualOperator ha N)≤C*(Real.log N^2+a⁻¹^2) := by
  obtain ⟨A,hA,havg⟩ := lemma_6_4
  obtain ⟨C,hC,hbound⟩ := residual_bound_of_average A hA
  refine ⟨C,hC,?_⟩
  intro N _ hN hlarge hGRH a ha0 ha
  exact hbound N inferInstance (large_parameters hlarge).1 hGRH
    (fun σ hσ hσβ => (havg N inferInstance hN hlarge hGRH σ hσ hσβ).2) a ha0 ha

theorem proposition_6_5 : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N),
    Even N → Real.exp 10 < (N : ℝ) → GRH N → ∀ ha : alpha N < beta,
      let α := alpha N
      let P := arithmeticOperator ha N
      let D := diagonalOperator ha N
      let K := modelOperator ha N
      IsPositiveTraceClass P ∧ IsPositiveTraceClass D ∧ IsHilbertSchmidt K ∧
      (hsNorm P ≤ positiveTrace P ∧
        positiveTrace P ≤ C * (Real.log N ^ 2 + α⁻¹ ^ 2)) ∧
      (hsNorm D ≤ positiveTrace D ∧ positiveTrace D ≤ C * α⁻¹ ^ 2) ∧
      hsNorm K ≤ C * α⁻¹ ^ 2 := by
  obtain ⟨A,hA,havg⟩ := lemma_6_4
  obtain ⟨C,hC,hbound⟩ := component_bounds_of_average A hA
  refine ⟨C,hC,?_⟩
  intro N _ hN hlarge hGRH ha
  exact hbound N inferInstance (large_parameters hlarge).1 hGRH
    (fun σ hσ hσβ => (havg N inferInstance hN hlarge hGRH σ hσ hσβ).2)
    (alpha N) (large_alpha_pos hlarge) ha

theorem lemma_A_3_absolute_operator_bound :
    ∃ C : ℝ, 0 < C ∧ EvenEventually (fun N => ∀ (_ : NeZero N), GRH N →
      ∀ a : ℝ, 0 < a → a < 1 / 10 → ∀ ha : a < beta,
        ‖residualOperator ha N‖ ≤ baselineBound C N a) := by
  obtain ⟨C,hC,hbound⟩ := residualOperator_uniform_hs_bound
  obtain ⟨k,hk⟩ := evenEventually_large
  refine ⟨C,hC,k,?_⟩
  intro N hNk hN _ hGRH a ha0 _ ha
  have h := hbound N inferInstance hN (hk N hNk hN) hGRH a ha0 ha
  exact h.2.1.trans h.2.2

theorem lemma_A_3 (φ : ℝ → ℝ) (hφ : IsWeight φ) :
    (∃ C L U : ℝ, 0 < C ∧ 0 < L ∧ 0 < U ∧
      EvenEventually (fun N => ∀ (_ : NeZero N), GRH N → ∀ a : ℝ, 0 < a → a < 1 / 10 →
        L * Real.rpow N (2 * a) ≤ normFunctional N φ a ∧
        normFunctional N φ a ≤ U * Real.rpow N (2 * a) ∧
        ∀ ha : a < beta, ‖residualOperator ha N‖ ≤ baselineBound C N a)) ∧
    Tendsto balanceFactor (nhdsWithin 0 (Ioi 0)) atTop ∧ Tendsto balanceFactor atTop atTop := by
  obtain ⟨C,hC,hbound⟩ := lemma_A_3_absolute_operator_bound
  obtain ⟨k,hk⟩ := hbound.and evenEventually_large
  have hE := weightEnergy_pos hφ
  refine ⟨⟨C,weightEnergy φ/6,weightEnergy φ,hC,by positivity,hE,k,?_⟩,
    balanceFactor_tendsto_zero,balanceFactor_tendsto_infty⟩
  intro N hNk hN _ hGRH a ha0 ha10
  obtain ⟨hB,hlarge⟩ := hk N hNk hN
  have hN4 := (large_parameters hlarge).1
  refine ⟨?_,?_,hB inferInstance hGRH a ha0 ha10⟩
  · simpa only [Real.rpow_eq_pow,mul_comm] using normFunctional_uniform_lower N (by omega) φ hφ a ha0 ha10
  · simpa only [Real.rpow_eq_pow,mul_comm] using normFunctional_uniform_upper N (by omega) φ hφ a ha0.le

lemma variable_uniform_spectral_bound (c : ℝ) (hc : 0<c) :
    ∃ C c₀ : ℝ, 1≤C ∧ 0<c₀ ∧ EvenEventually (fun N =>
      ∀ (_ : NeZero N) (ha : alpha N c<beta), GRH N →
        IsHilbertSchmidt (residualOperator ha N) ∧
        ‖residualOperator ha N‖≤hsNorm (residualOperator ha N) ∧
        hsNorm (residualOperator ha N)≤C*Real.log N^2 ∧
        SpectralZeroFree N (alpha N c) ha (c₀*singularSeries N/(N*Real.log N))) := by
  obtain ⟨A,hA,hbound⟩ := residualOperator_uniform_hs_bound
  let C := A*(1+c⁻¹^2)+1
  have hC : 1≤C := by
    dsimp [C]
    have : 0≤A*(1+c⁻¹^2) := by positivity
    linarith
  have hCp : 0<C := by linarith
  refine ⟨C,1/(16*C^2),hC,by positivity,?_⟩
  obtain ⟨k,hk⟩ := evenEventually_large
  refine ⟨k,?_⟩
  intro N hNk hN _ ha hGRH
  have hlarge := hk N hNk hN
  have hN4 := (large_parameters hlarge).1
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hlog : 10<Real.log N := (Real.lt_log_iff_exp_lt hn).mpr hlarge
  have ha0 := alpha_pos_at N hN4 c hc
  obtain ⟨hhs,hnorm,hh⟩ := hbound N inferInstance hN hlarge hGRH _ ha0 ha
  have he : A*(Real.log N^2+(alpha N c)⁻¹^2)=A*(1+c⁻¹^2)*Real.log N^2 := by
    simp only [alpha,div_eq_mul_inv,mul_inv,inv_inv,mul_pow]
    ring
  rw [he] at hh
  have hhsC : hsNorm (residualOperator ha N)≤C*Real.log N^2 := by
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _)
  refine ⟨hhs,hnorm,hhsC,?_⟩
  apply spectralZeroFree_of_log_square_bound _ N ha0 hN4 hGRH ha (by linarith) _ C hC (hnorm.trans hhsC)
  apply (singularSeries_upper_totient N hN (by omega)).trans
  exact div_le_self hn.le (by exact_mod_cast Nat.totient_pos.mpr (show 0<N by omega))

theorem theorem_6_2 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    EvenEventually (fun N => ∀ (_ : NeZero N) (ha : alpha N < beta), GRH N →
      IsHilbertSchmidt (residualOperator ha N) ∧
      ‖residualOperator ha N‖ ≤ hsNorm (residualOperator ha N) ∧
      hsNorm (residualOperator ha N) ≤ C * Real.log N ^ 2 ∧
      SpectralZeroFree N (alpha N) ha (c * singularSeries N / (N * Real.log N))) := by
  obtain ⟨C,c,hC,hc,hb⟩ := variable_uniform_spectral_bound 1 (by norm_num)
  exact ⟨C,c,by linarith,hc,hb⟩

end LiLiuGoldbach16
