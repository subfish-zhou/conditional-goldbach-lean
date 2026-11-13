import ConditionalGoldbach.Proofs.VariableWeightNorm
import ConditionalGoldbach.Proofs.SpectralAlgebra

/-! Uniform comparison of the functional norm, baseline bound, and spectral widths. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma baselineBound_alpha (C : ℝ) (N : ℕ) (c : ℝ) :
    baselineBound C N (alpha N c) = C*Real.log N^2*(1+c⁻¹^2) := by
  simp only [baselineBound, alpha, div_eq_mul_inv, mul_inv, inv_inv]
  ring

lemma normFunctional_baseline_bounds (φ : ℝ → ℝ) (hφ : IsWeight φ) (C : ℝ) (hC : 0 < C)
    (N : ℕ) (hN : 4 ≤ N) (c : ℝ) (hc : 0 < c) (ha : alpha N c < 1/10) :
    (C*weightEnergy φ/6)*Real.log N^2*balanceFactor c ≤
        normFunctional N φ (alpha N c)*baselineBound C N (alpha N c) ∧
    normFunctional N φ (alpha N c)*baselineBound C N (alpha N c) ≤
        (C*weightEnergy φ)*Real.log N^2*balanceFactor c := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have ha0 : 0 < alpha N c := div_pos hc hlog
  have hlo := normFunctional_uniform_lower N (by omega) φ hφ (alpha N c) ha0 ha
  have hhi := normFunctional_uniform_upper N (by omega) φ hφ (alpha N c) ha0.le
  rw [nat_rpow_alpha N (by omega)] at hlo hhi
  have hb : 0 ≤ baselineBound C N (alpha N c) := by unfold baselineBound; positivity
  have hl := mul_le_mul_of_nonneg_right hlo hb
  have hu := mul_le_mul_of_nonneg_right hhi hb
  rw [baselineBound_alpha] at hl hu ⊢
  unfold balanceFactor
  constructor
  · convert hl using 1 <;> ring
  · convert hu using 1 <;> ring

theorem lemma_A_3_balance (φ : ℝ → ℝ) (hφ : IsWeight φ) (C : ℝ) (hC : 0 < C) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ EvenEventually (fun N =>
      ∀ c : ℝ, 0 < c → alpha N c < 1 / 10 →
        L * Real.log N ^ 2 * balanceFactor c ≤
          normFunctional N φ (alpha N c) * baselineBound C N (alpha N c) ∧
        normFunctional N φ (alpha N c) * baselineBound C N (alpha N c) ≤
          U * Real.log N ^ 2 * balanceFactor c ∧
        ∀ h : ℕ → ℝ, 0 < h N →
          L ^ 2 * h N ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2 ≤
            h N ^ 2 * (normFunctional N φ (alpha N c) * baselineBound C N (alpha N c)) ^ 2 /
              singularSeries N ^ 2 ∧
          h N ^ 2 * (normFunctional N φ (alpha N c) * baselineBound C N (alpha N c)) ^ 2 /
              singularSeries N ^ 2 ≤
            U ^ 2 * h N ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2) := by
  let L := C*weightEnergy φ/6
  let U := C*weightEnergy φ
  have hE := weightEnergy_pos hφ
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  refine ⟨L,U,hL,hU,4,fun N hN _ c hc ha => ?_⟩
  obtain ⟨hl,hu⟩ := normFunctional_baseline_bounds φ hφ C hC N hN c hc ha
  change L*Real.log N^2*balanceFactor c ≤ _ at hl
  change _ ≤ U*Real.log N^2*balanceFactor c at hu
  refine ⟨hl,hu,fun h hh => ?_⟩
  have hbal : 0 ≤ balanceFactor c := by unfold balanceFactor; positivity
  have hlo0 : 0 ≤ L*Real.log N^2*balanceFactor c := by positivity
  have hprod0 := hlo0.trans hl
  have hl2 := pow_le_pow_left₀ hlo0 hl 2
  have hu2 := pow_le_pow_left₀ hprod0 hu 2
  have hscale : 0 ≤ h N^2/singularSeries N^2 := by positivity
  have hl' := mul_le_mul_of_nonneg_left hl2 hscale
  have hu' := mul_le_mul_of_nonneg_left hu2 hscale
  constructor
  · convert hl' using 1 <;> ring
  · convert hu' using 1 <;> ring

lemma spectralWidth_ratio_bounds (N : ℕ) (r s : ℝ)
    (hd : 0 < spectralScale N) (hr : spectralScale N < r) (hs : spectralScale N < s) :
    s^2/(2*r^2) ≤ spectralWidthFromBound N r / spectralWidthFromBound N s ∧
      spectralWidthFromBound N r / spectralWidthFromBound N s ≤ 2*s^2/r^2 := by
  have hr0 : 0 < r := hd.trans hr
  have hs0 : 0 < s := hd.trans hs
  obtain ⟨hrl,hru⟩ := theorem_6_1_width_comparison N r hd hr
  obtain ⟨hsl,hsu⟩ := theorem_6_1_width_comparison N s hd hs
  have her0 : 0 < spectralWidthFromBound N r := lt_of_lt_of_le (by positivity) hrl
  have hes0 : 0 < spectralWidthFromBound N s := lt_of_lt_of_le (by positivity) hsl
  constructor
  · have hh := div_le_div₀ her0.le hrl hes0 hsu
    have he : (spectralScale N^2/(4*r^2))/(spectralScale N^2/(2*s^2)) = s^2/(2*r^2) := by
      field_simp
      <;> ring
    rwa [he] at hh
  · have hh := div_le_div₀ (by positivity : 0 ≤ spectralScale N^2/(2*r^2)) hru
      (by positivity : 0 < spectralScale N^2/(4*s^2)) hsl
    have he : (spectralScale N^2/(2*r^2))/(spectralScale N^2/(4*s^2)) = 2*s^2/r^2 := by
      field_simp
      <;> ring
    rwa [he] at hh

theorem lemma_A_3_width_ratio (φ : ℝ → ℝ) (hφ : IsWeight φ)
    (C : ℝ) (hC : 0 < C) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ EvenEventually (fun N =>
      ∀ c h : ℝ, 0 < c → alpha N c < 1 / 10 → 0 < h →
        let requiredNorm := singularSeries N / (h * normFunctional N φ (alpha N c))
        let suppliedNorm := baselineBound C N (alpha N c)
        let requiredWidth := spectralWidthFromBound N requiredNorm
        let suppliedWidth := spectralWidthFromBound N suppliedNorm
        0 < spectralScale N → spectralScale N < requiredNorm →
        spectralScale N < suppliedNorm → requiredWidth ≤ 1 / 4 →
        suppliedWidth ≤ 1 / 4 →
          L * h ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2 ≤
            requiredWidth / suppliedWidth ∧
          requiredWidth / suppliedWidth ≤
            U * h ^ 2 * Real.log N ^ 4 / singularSeries N ^ 2 * balanceFactor c ^ 2)  := by
  obtain ⟨L,U,hL,hU,N₀,hbound⟩ := lemma_A_3_balance φ hφ C hC
  refine ⟨L^2/2, 2*U^2, by positivity, by positivity, N₀, ?_⟩
  intro N hN heven c h hc ha hh
  dsimp only
  intro hd hr hs _ _
  let Q := normFunctional N φ (alpha N c)
  let B := baselineBound C N (alpha N c)
  have hr0 : 0 < singularSeries N/(h*Q) := hd.trans hr
  have hQ : Q ≠ 0 := by intro he; simp [he] at hr0
  have hS : singularSeries N ≠ 0 := by intro he; simp [he] at hr0
  have he : B^2/(singularSeries N/(h*Q))^2 = h^2*(Q*B)^2/singularSeries N^2 := by
    field_simp
    <;> ring
  obtain ⟨hl,hu⟩ := (hbound N hN heven c hc ha).2.2 (fun _ => h) hh
  obtain ⟨hrl,hru⟩ := spectralWidth_ratio_bounds N (singularSeries N/(h*Q)) B hd hr hs
  change _ ≤ spectralWidthFromBound N (singularSeries N/(h*Q))/spectralWidthFromBound N B ∧
    spectralWidthFromBound N (singularSeries N/(h*Q))/spectralWidthFromBound N B ≤ _
  have hel : B^2/(2*(singularSeries N/(h*Q))^2) =
      (h^2*(Q*B)^2/singularSeries N^2)/2 := by rw [show B^2/(2*(singularSeries N/(h*Q))^2) = (B^2/(singularSeries N/(h*Q))^2)/2 by ring, he]
  have heu : 2*B^2/(singularSeries N/(h*Q))^2 =
      2*(h^2*(Q*B)^2/singularSeries N^2) := by rw [show 2*B^2/(singularSeries N/(h*Q))^2 = 2*(B^2/(singularSeries N/(h*Q))^2) by ring, he]
  rw [hel] at hrl
  rw [heu] at hru
  constructor
  · have hl' := div_le_div_of_nonneg_right hl (by norm_num : (0:ℝ) ≤ 2)
    convert hl'.trans hrl using 1 <;> ring
  · have hu' := mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ 2)
    convert hru.trans hu' using 1 <;> ring

end ConditionalGoldbach
