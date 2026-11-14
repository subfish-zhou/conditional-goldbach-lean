module

public import ConditionalGoldbach.Proofs.QuantitativeBounds

/-! The full parameterized spectral and arithmetic conclusions, with their shared constant. -/
public section

set_option autoImplicit false
noncomputable section
open Set Filter
namespace ConditionalGoldbach

lemma evenEventually_variable_large (c : ℝ) :
    EvenEventually (fun N => 4≤N ∧ Real.exp (10*c)<(N:ℝ)) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 4 (Real.exp (10*c)))
  refine ⟨k,?_⟩
  intro N hN hEven
  have hNk : (k:ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · exact_mod_cast (show (4:ℝ) ≤ N from ((le_max_left _ _).trans hk.le).trans hNk)
  · exact ((le_max_right _ _).trans_lt hk).trans_le hNk

theorem proposition_A_2 (φ : ℝ → ℝ) (hφ : IsWeight φ) (c : ℝ) (hc : 0 < c) :
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → Real.exp (10 * c) < (N : ℝ) → GRH N →
      ∀ ha : alpha N c < beta,
      (SpectralR N (alpha N c) ha ↔ ‖residualOperator ha N‖ ≤ spectralScale N) ∧
      (∀ η : ℝ, 0 < η → η < 1 / 2 → (SpectralZeroFree N (alpha N c) ha η ↔
        ‖residualOperator ha N‖ ≤ spectralScale N / (2 * Real.sqrt (η * (1 - η))))) ∧
      (∀ h : ℕ → ℝ, 0 < h N → 0 < zeroFreeWidth N h → zeroFreeWidth N h ≤ 1 / 4 →
        (SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h) ↔
          ‖residualOperator ha N‖ ≤ singularSeries N / (2 * h N * Real.sqrt (1 - zeroFreeWidth N h))))) ∧
    (∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧
      EvenEventually (fun N => ∀ (_ : NeZero N) (ha : alpha N c < beta), GRH N →
        ‖residualOperator ha N‖ ≤ C * Real.log N ^ 2 ∧
        SpectralZeroFree N (alpha N c) ha (c₀ * singularSeries N / (N * Real.log N))) ∧
      (∀ h : ℕ → ℝ, HypothesisSAt c h →
        EvenEventually (fun N => GRH N →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * singularSeries N / h N)) ∧
      (HypothesisRAt c →
        EvenEventually (fun N => GRH N →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N))) := by
  constructor
  · intro N hNZ hN hN4 hlarge hGRH ha
    have hd := variable_spectral_dictionary (alpha N c) (alpha_pos_at N hN4 c hc) N hN4 hGRH ha
    refine ⟨hd.1,hd.2,?_⟩
    intro h hh hη hηsmall
    have he := spectralScale_div_sqrt_width_eq N h
      (by exact_mod_cast (show 0<N by omega)) (singularSeries_pos N)
      (Real.log_pos (by exact_mod_cast (show 1<N by omega))) hh (by linarith)
    rw [← he]
    exact hd.2 _ hη (by linarith)
  · obtain ⟨A,c₀,hA,hc₀,huniform⟩ := variable_uniform_spectral_bound c hc
    obtain ⟨B,hB,hpoint⟩ := proposition_A_2_pointwise φ hφ c hc
    have hA0 : 0<A := by linarith
    have hAB : A≤A+B := le_add_of_nonneg_right hB.le
    have hBA : B≤A+B := le_add_of_nonneg_left hA0.le
    refine ⟨A+B,c₀,by positivity,hc₀,?_,?_,?_⟩
    · apply huniform.mono
      intro N hN hNZ ha hGRH
      have hh := hN hNZ ha hGRH
      exact ⟨hh.2.1.trans (hh.2.2.1.trans (mul_le_mul_of_nonneg_right hAB (sq_nonneg _))),hh.2.2.2⟩
    · intro h hS
      obtain ⟨k,hk⟩ := hS.2.and (hS.1.2.2.and (evenEventually_variable_large c))
      refine ⟨k,?_⟩
      intro N hNk hN hGRH
      obtain ⟨hwidth,hηsmall,hN4,hlarge⟩ := hk N hNk hN
      let : NeZero N := ⟨by omega⟩
      have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
      have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
      have hh : 0<h N := hS.1.1 N hN hN4
      have hSp := singularSeries_pos N
      have hη : 0<zeroFreeWidth N h := by unfold zeroFreeWidth; positivity
      have ha10 := (variable_parameters N hN4 c hc hlarge).2.1
      have ha : alpha N c<beta := by unfold beta; linarith
      have hb := (hpoint N inferInstance hN hN4 hlarge hGRH ha).1 h hh hη hηsmall
        (hwidth hGRH inferInstance ha)
      apply hb.trans
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBA (singularSeries_pos N).le) hh.le
    · intro hR
      obtain ⟨k,hk⟩ := hR.and (evenEventually_variable_large c)
      refine ⟨k,?_⟩
      intro N hNk hN hGRH
      obtain ⟨hR',hN4,hlarge⟩ := hk N hNk hN
      let : NeZero N := ⟨by omega⟩
      have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
      have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
      have ha10 := (variable_parameters N hN4 c hc hlarge).2.1
      have ha : alpha N c<beta := by unfold beta; linarith
      have hb := (hpoint N inferInstance hN hN4 hlarge hGRH ha).2 (hR' hGRH inferInstance ha)
      exact hb.trans (mul_le_mul_of_nonneg_right hBA (spectralScale_pos N hNp (singularSeries_pos N) hlog).le)

end ConditionalGoldbach
