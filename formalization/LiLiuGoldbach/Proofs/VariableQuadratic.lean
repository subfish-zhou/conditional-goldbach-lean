import LiLiuGoldbach.Proofs.VariableStripOperators
import LiLiuGoldbach.Proofs.VariableWeightAsymptotic
import LiLiuGoldbach.Proofs.QuadraticIdentity
import LiLiuGoldbach.Proofs.DictionaryApplication

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16

lemma variable_parameters (N : ℕ) (hN4 : 4 ≤ N) (c : ℝ) (hc : 0<c)
    (hlarge : Real.exp (10*c) < (N : ℝ)) :
    0 < alpha N c ∧ alpha N c < 1/10 ∧ 1/40 < width (alpha N c) ∧
      1/90 < sigmaStar-alpha N c ∧ beta-sigmaStar=1/72 := by
  have hl : 10*c < Real.log N := by simpa using Real.log_lt_log (Real.exp_pos (10*c)) hlarge
  have hl0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have ha : alpha N c < 1/10 := by
    unfold alpha
    apply (div_lt_div_iff₀ hl0 (by norm_num : (0:ℝ)<10)).2
    nlinarith
  exact ⟨alpha_pos_at N hN4 c hc,ha,by dsimp [width,beta]; linarith,
    by dsimp [sigmaStar]; linarith,by norm_num [beta,sigmaStar]⟩

lemma residual_quadratic_at (a : ℝ) (ha0 : 0<a) (ha10 : a<1/10) (N : ℕ) [NeZero N] (hN : Even N)
    (hN4 : 4 ≤ N) (hGRH : GRH N)
    (φ : ℝ → ℝ) (hφ : IsWeight φ) (ha : a < beta) :
    (weightMass φ * singularSeries N - goldbach N φ : ℝ) =
      paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) ∧
    |weightMass φ * singularSeries N - goldbach N φ| ≤
      normFunctional N φ a * ‖residualOperator ha N‖ := by
  have hσ : sigmaStar ∈ Ioo a beta := ⟨by dsimp [sigmaStar]; linarith,by norm_num [sigmaStar,beta]⟩
  have hσ0 : 0 < sigmaStar := by norm_num [sigmaStar]
  have heq : (weightMass φ * singularSeries N - goldbach N φ : ℝ) =
      paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) := by
    rw [quadratic_residual_integral N φ hφ sigmaStar hσ hσ0 hσ (residualOperator ha N)
      (fun s z hs hz => residualOperator_pairing_at a N ha0 hN4 hGRH ha s z hs hz)]
    exact (proposition_7_3 N hN hN4 hGRH φ hφ sigmaStar hσ0 (by norm_num [sigmaStar])).symm
  refine ⟨heq, ?_⟩
  have hn := (rieszVector_density_spec N (by omega) φ hφ hσ).2
  rw [← normFunctional_density_integral N (by omega)] at hn
  have hbound : ‖paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ)‖ ≤
      ‖(rieszVector N φ : HardySpace a beta)‖ ^ 2 * ‖residualOperator ha N‖ := by
    unfold paperInner
    calc
      _ ≤ ‖(rieszVector N φ : HardySpace a beta)‖ *
          ‖residualOperator ha N (rieszVector N φ)‖ := norm_inner_le_norm _ _
      _ ≤ ‖(rieszVector N φ : HardySpace a beta)‖ *
          (‖residualOperator ha N‖ * ‖(rieszVector N φ : HardySpace a beta)‖) :=
        mul_le_mul_of_nonneg_left ((residualOperator ha N).le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  rw [← heq, Complex.norm_real, Real.norm_eq_abs, hn] at hbound
  exact hbound

theorem proposition_A_1 (φ : ℝ → ℝ) (hφ : IsWeight φ) (c : ℝ) (hc : 0 < c) :
    (∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N → Real.exp (10 * c) < (N : ℝ) → GRH N →
      alpha N c < 1 / 10 ∧ 1 / 40 < width (alpha N c) ∧
      1 / 90 < sigmaStar - alpha N c ∧ beta - sigmaStar = 1 / 72 ∧
      (∀ σ ∈ Ioo (alpha N c) beta,
        (∀ h : HardySpace (alpha N c) beta,
          Integrable (fun t : ℝ => (N : ℂ) ^ (line σ t) * mellinWeight φ (line σ t) *
            (1 + line σ t) * fourierLaplace h (line σ t)) ∧
          functionalValue N φ σ h = paperInner h (rieszVector N φ)) ∧
        ∃ ℓ : HardySpace (alpha N c) beta →L[ℂ] ℂ,
          (∀ h, ℓ h = functionalValue N φ σ h) ∧
          ‖ℓ‖ ^ 2 = normFunctional N φ (alpha N c)) ∧
      ‖(rieszVector N φ : HardySpace (alpha N c) beta)‖ ^ 2 = normFunctional N φ (alpha N c) ∧
      (∀ ha : alpha N c < beta,
        IsCompactOperator (residualOperator ha N) ∧ IsSelfAdjoint (residualOperator ha N) ∧
        IsHilbertSchmidt (residualOperator ha N) ∧
        (∀ s z : ℂ, s ∈ strip (alpha N c) beta → z ∈ strip (alpha N c) beta →
          ‖residual N s (conj z)‖ ≤ ‖residualOperator ha N‖ * ‖1 + s‖ * ‖1 + z‖ /
            (8 * Real.sqrt (pointDistance (alpha N c) beta s * pointDistance (alpha N c) beta z))) ∧
        (weightMass φ * singularSeries N - goldbach N φ : ℝ) =
          paperInner (residualOperator ha N (rieszVector N φ)) (rieszVector N φ) ∧
        |weightMass φ * singularSeries N - goldbach N φ| ≤
          normFunctional N φ (alpha N c) * ‖residualOperator ha N‖) ∧
      normFunctional N φ (alpha N c) ≤ Real.exp (2 * c) * weightEnergy φ) ∧
    (∃ C : ℝ, 0 < C ∧ EvenEventually (fun N =>
      |normFunctional N φ (alpha N c) - Real.exp (2 * c) * weightEnergy φ| ≤ C / Real.log N))  := by
  refine ⟨?_,normFunctional_asymptotic_at c hc φ hφ⟩
  intro N hNZ hN hN4 hlarge hGRH
  obtain ⟨ha0,ha10,hw,hd,hβ⟩ := variable_parameters N hN4 c hc hlarge
  have hstar : sigmaStar ∈ Ioo (alpha N c) beta := ⟨by linarith,by norm_num [sigmaStar,beta]⟩
  have hNpos : 0 < N := by omega
  obtain ⟨hv,hn⟩ := rieszVector_density_spec N hNpos φ hφ hstar
  rw [← normFunctional_density_integral N hNpos] at hn
  have hu := normFunctional_uniform_upper N hNpos φ hφ (alpha N c) ha0.le
  rw [nat_rpow_alpha N (by omega) c] at hu
  refine ⟨ha10,hw,hd,hβ,?_,hn,?_,hu⟩
  · intro σ hσ
    constructor
    · intro h
      exact ⟨functionalValue_integrable N hNpos φ hφ σ hσ h,hv σ hσ h⟩
    · obtain ⟨ℓ,hℓ,hnorm⟩ := functionalValue_continuousLinearMap N hNpos φ hφ σ hσ
      rw [← normFunctional_density_integral N hNpos] at hnorm
      exact ⟨ℓ,hℓ,hnorm⟩
  · intro ha
    have hs := residualOperator_spec_at (alpha N c) N ha0 hN4 hGRH ha
    refine ⟨hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,?_,
      residual_quadratic_at (alpha N c) ha0 ha10 N hN hN4 hGRH φ hφ ha⟩
    intro s z hs hz
    exact residual_norm_le_of_kernel_pairing ha ha0.le N (residualOperator ha N) s z hs hz
      (residualOperator_pairing_at (alpha N c) N ha0 hN4 hGRH ha s z hs hz)

lemma variable_spectral_dictionary (a : ℝ) (ha0 : 0<a) (N : ℕ) [NeZero N]
    (hN4 : 4 ≤ N) (hGRH : GRH N) (ha : a < beta) :
    (SpectralR N a ha ↔ ‖residualOperator ha N‖ ≤ spectralScale N) ∧
    (∀ η : ℝ, 0 < η → η < 1/2 → (SpectralZeroFree N a ha η ↔
      ‖residualOperator ha N‖ ≤ spectralScale N/(2*Real.sqrt (η*(1-η))))) := by
  have hs := (residualOperator_spec_at a N ha0 hN4 hGRH ha).2.2.2.2.2.1
  have hδ := spectralScale_pos N (by exact_mod_cast (show 0<N by omega)) (singularSeries_pos N)
    (Real.log_pos (by exact_mod_cast (show 1<N by omega)))
  exact theorem_6_1_abstract_dictionary N (residualOperator ha N) hs hδ

theorem proposition_A_2_pointwise (φ : ℝ → ℝ) (hφ : IsWeight φ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), Even N → 4 ≤ N →
      Real.exp (10 * c) < (N : ℝ) → GRH N → ∀ ha : alpha N c < beta,
        (∀ h : ℕ → ℝ, 0 < h N → 0 < zeroFreeWidth N h → zeroFreeWidth N h ≤ 1 / 4 →
          SpectralZeroFree N (alpha N c) ha (zeroFreeWidth N h) →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * singularSeries N / h N) ∧
        (SpectralR N (alpha N c) ha →
          |goldbach N φ - weightMass φ * singularSeries N| ≤ C * spectralScale N)  := by
  let C := Real.exp (2*c)*weightEnergy φ
  have hC : 0<C := mul_pos (Real.exp_pos _) (weightEnergy_pos hφ)
  refine ⟨C,hC,?_⟩
  intro N hNZ hN hN4 hlarge hGRH ha
  have ha0 := alpha_pos_at N hN4 c hc
  have hA := (proposition_A_1 φ hφ c hc).1 N hNZ hN hN4 hlarge hGRH
  have herr : |goldbach N φ-weightMass φ*singularSeries N| ≤ C*‖residualOperator ha N‖ := by
    apply le_trans _ (mul_le_mul_of_nonneg_right hA.2.2.2.2.2.2.2 (norm_nonneg _))
    simpa only [abs_sub_comm] using (hA.2.2.2.2.2.2.1 ha).2.2.2.2.2
  have hd := variable_spectral_dictionary (alpha N c) ha0 N hN4 hGRH ha
  constructor
  · intro h hh hη hη' hz
    have hn := (hd.2 _ hη (by linarith)).1 hz
    have hs := spectralScale_div_sqrt_width_le N h (by exact_mod_cast (show 0<N by omega))
      (singularSeries_pos N) (Real.log_pos (by exact_mod_cast (show 1<N by omega))) hh hη'
    calc
      _ ≤ C*‖residualOperator ha N‖ := herr
      _ ≤ C*(singularSeries N/h N) := mul_le_mul_of_nonneg_left (hn.trans hs) hC.le
      _ = _ := by ring
  · intro hR
    exact herr.trans (mul_le_mul_of_nonneg_left (hd.1.mp hR) hC.le)

end LiLiuGoldbach16
