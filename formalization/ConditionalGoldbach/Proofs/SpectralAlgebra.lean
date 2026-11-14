module

public import ConditionalGoldbach.Analysis.SpectralData
public import ConditionalGoldbach.Definitions.Hypotheses
public import Mathlib.Algebra.Ring.IsFormallyReal

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

/-- The logical R-to-S implication uses only the eventual upper bound on the
prescribed width; it does not depend on the analytic spectral dictionary. -/
theorem theorem_1_2_hypothesisR_implies_S (hR : HypothesisR)
    (h : ℕ → ℝ) (hh : IsAdmissible h) : HypothesisS h := by
  rcases hR with ⟨NR, hNR⟩
  rcases hh.2.2 with ⟨NS, hNS⟩
  refine ⟨hh, max NR NS, ?_⟩
  intro N hN heven hGRH hNZ ha q hq hzero
  have hcrit := hNR N (le_trans (le_max_left NR NS) hN) heven hGRH hNZ ha q hzero
  have hwidth := hNS N (le_trans (le_max_right NR NS) hN) heven
  change 1 - zeroFreeWidth N h < q.re at hq
  linarith

/-- Rationalized-square-root bounds, with the paper's strict hypotheses. -/
theorem theorem_6_1_width_comparison (N : ℕ) (M : ℝ)
    (hδ : 0 < spectralScale N) (hM : spectralScale N < M) :
    spectralScale N ^ 2 / (4 * M ^ 2) ≤ spectralWidthFromBound N M ∧
      spectralWidthFromBound N M ≤ spectralScale N ^ 2 / (2 * M ^ 2) := by
  have hMpos : 0 < M := lt_trans hδ hM
  have hM2pos : 0 < M ^ 2 := sq_pos_of_pos hMpos
  have hratio_nonneg : 0 ≤ spectralScale N ^ 2 / M ^ 2 := div_nonneg (sq_nonneg _) (le_of_lt hM2pos)
  have hratio_le : spectralScale N ^ 2 / M ^ 2 ≤ 1 := by
    apply (div_le_one hM2pos).2
    nlinarith
  have harg_nonneg : 0 ≤ 1 - spectralScale N ^ 2 / M ^ 2 := sub_nonneg.mpr hratio_le
  have hsqrt_nonneg := Real.sqrt_nonneg (1 - spectralScale N ^ 2 / M ^ 2)
  have hsqrt_sq := Real.sq_sqrt harg_nonneg
  have hsqrt_le : Real.sqrt (1 - spectralScale N ^ 2 / M ^ 2) ≤ 1 := by
    apply (Real.sqrt_le_one).2
    linarith
  have hleft : spectralScale N ^ 2 / (4 * M ^ 2) = (spectralScale N ^ 2 / M ^ 2) / 4 := by ring
  have hright : spectralScale N ^ 2 / (2 * M ^ 2) = (spectralScale N ^ 2 / M ^ 2) / 2 := by ring
  rw [hleft, hright]
  unfold spectralWidthFromBound
  constructor
  · nlinarith [sq_nonneg (Real.sqrt (1 - spectralScale N ^ 2 / M ^ 2) - 1)]
  · nlinarith [mul_nonneg hsqrt_nonneg (sub_nonneg.mpr hsqrt_le)]

/-- The exact relation between the spectral scale and its elementary square. -/
theorem spectralScale_sq (N : ℕ) (hN : 0 < (N : ℝ))
    (hS : 0 ≤ singularSeries N) (hlog : 0 ≤ Real.log N) :
    spectralScale N ^ 2 = (singularSeries N / N) * Real.log N ^ 3 := by
  unfold spectralScale
  rw [mul_pow, Real.sq_sqrt (div_nonneg hS hN.le)]
  congr 1
  rw [Real.rpow_eq_pow, ← Real.rpow_mul_natCast hlog (3 / 2) 2]
  norm_num

/-- Positivity is supplied explicitly rather than inferred from totalized roots. -/
theorem spectralScale_pos (N : ℕ) (hN : 0 < (N : ℝ))
    (hS : 0 < singularSeries N) (hlog : 0 < Real.log N) :
    0 < spectralScale N := by
  unfold spectralScale
  exact mul_pos (Real.sqrt_pos.2 (div_pos hS hN)) (Real.rpow_pos_of_pos hlog _)

/-- The S-width gives the norm bound S(N)/h(N); a sharp numerical constant is
unnecessary for the uniform big-O statement in Theorem 1.1. -/
theorem spectralScale_div_sqrt_width_le (N : ℕ) (h : ℕ → ℝ)
    (hN : 0 < (N : ℝ)) (hS : 0 < singularSeries N)
    (hlog : 0 < Real.log N) (hh : 0 < h N)
    (hwidth : zeroFreeWidth N h ≤ 1 / 4) :
    spectralScale N / (2 * Real.sqrt (zeroFreeWidth N h * (1 - zeroFreeWidth N h))) ≤
      singularSeries N / h N := by
  let η := zeroFreeWidth N h
  have hη : 0 < η := by
    dsimp [η, zeroFreeWidth]
    positivity
  have hηupper : η ≤ 1 / 4 := hwidth
  have hηone : 0 < 1 - η := by linarith
  have hr : 0 < Real.sqrt (η * (1 - η)) := Real.sqrt_pos.2 (mul_pos hη hηone)
  have hrsq : Real.sqrt (η * (1 - η)) ^ 2 = η * (1 - η) :=
    Real.sq_sqrt (mul_pos hη hηone).le
  have hδ : 0 < spectralScale N := spectralScale_pos N hN hS hlog
  have hid : (spectralScale N * h N) ^ 2 = singularSeries N ^ 2 * η := by
    rw [mul_pow, spectralScale_sq N hN hS.le hlog.le]
    dsimp [η, zeroFreeWidth]
    field_simp
  have hηbound : η ≤ 4 * (η * (1 - η)) := by
    nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hηupper)]
  have hsqbound : (spectralScale N * h N) ^ 2 ≤
      (2 * Real.sqrt (η * (1 - η)) * singularSeries N) ^ 2 := by
    calc
      _ = singularSeries N ^ 2 * η := hid
      _ ≤ singularSeries N ^ 2 * (4 * (η * (1 - η))) :=
        mul_le_mul_of_nonneg_left hηbound (sq_nonneg _)
      _ = _ := by simp only [mul_pow, hrsq]; ring
  have hbound : spectralScale N * h N ≤
      2 * Real.sqrt (η * (1 - η)) * singularSeries N :=
    (sq_le_sq₀ (mul_pos hδ hh).le (by positivity)).mp hsqbound
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hr)).2
  convert (le_div_iff₀ hh).2 hbound using 1
  ring

/-- The central quadratic factor has exactly the double zero claimed in §6.3.
This statement is purely algebraic and analytic, independent of GRH or a spectrum. -/
theorem quadratic_factor_central_order (δ μ : ℝ) (hμ : μ ≠ 0)
    (hd : δ ^ 2 / μ ^ 2 = 1) :
    analyticOrderNatAt (fun q : ℂ =>
      1 - (4 * μ ^ 2 / δ ^ 2 : ℝ) * q * (1 - q)) (1 / 2) = 2 := by
  have hsq : δ ^ 2 = μ ^ 2 := (div_eq_one_iff_eq (pow_ne_zero 2 hμ)).mp hd
  have hcoeff : 4 * μ ^ 2 / δ ^ 2 = 4 := by rw [hsq]; field_simp
  simp only [hcoeff, Complex.ofReal_ofNat]
  have hfun : (fun q : ℂ => 1 - 4 * q * (1 - q)) =
      (fun _ : ℂ => 4) * ((fun q : ℂ => q - 1 / 2) ^ 2) := by
    funext q
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  rw [hfun, analyticOrderNatAt, analyticOrderAt_mul (by fun_prop) (by fun_prop)]
  have hconst : analyticOrderAt (fun _ : ℂ => (4 : ℂ)) (1 / 2) = 0 := by
    apply analyticOrderAt_eq_zero.2
    norm_num
  rw [hconst, analyticOrderAt_centeredMonomial]
  norm_num

set_option linter.unusedVariables false in
/-- The audited paper clause, specialized from the unconditional factor lemma. -/
theorem proposition_6_3_factor_central_order (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) (j : ℕ)
    (hμ : eigenvalues (residualOperator ha N) j ≠ 0)
    (hd : spectralRootParameter N (eigenvalues (residualOperator ha N) j) = 1) :
    analyticOrderNatAt (fun q : ℂ =>
      1 - (4 * eigenvalues (residualOperator ha N) j ^ 2 / spectralScale N ^ 2 : ℝ) *
        q * (1 - q)) (1 / 2) = 2 := by
  exact quadratic_factor_central_order _ _ hμ hd

section SpectralNormalization
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] theorem spectralPartialQuaternion_zero (N : ℕ) (T : H →L[ℂ] H) (k : ℕ) :
    spectralPartialQuaternion N T 0 k = 1 := by
  simp [spectralPartialQuaternion]

@[simp] theorem spectralPartialQuaternion_one (N : ℕ) (T : H →L[ℂ] H) (k : ℕ) :
    spectralPartialQuaternion N T 1 k = 1 := by
  simp [spectralPartialQuaternion]

theorem spectralPartialQuaternion_one_sub (N : ℕ) (T : H →L[ℂ] H)
    (q : Quaternion ℝ) (k : ℕ) :
    spectralPartialQuaternion N T (1 - q) k = spectralPartialQuaternion N T q k := by
  have hq : (1 - q) * (1 - (1 - q)) = q * (1 - q) := by noncomm_ring
  simp only [spectralPartialQuaternion, hq]

@[simp] theorem spectralQuaternion_zero (N : ℕ) (T : H →L[ℂ] H) :
    spectralQuaternion N T 0 = 1 := by
  have hlim : Tendsto (spectralPartialQuaternion N T 0) atTop (𝓝 1) := by
    change Tendsto (fun k => spectralPartialQuaternion N T 0 k) atTop (𝓝 1)
    simpa only [spectralPartialQuaternion_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : Quaternion ℝ)) atTop (𝓝 1))
  have hex : ∃ y, Tendsto (spectralPartialQuaternion N T 0) atTop (𝓝 y) := ⟨1, hlim⟩
  unfold spectralQuaternion
  rw [dite_eq_left hex]
  exact tendsto_nhds_unique (Classical.choose_spec hex) hlim

@[simp] theorem spectralQuaternion_one (N : ℕ) (T : H →L[ℂ] H) :
    spectralQuaternion N T 1 = 1 := by
  have hlim : Tendsto (spectralPartialQuaternion N T 1) atTop (𝓝 1) := by
    change Tendsto (fun k => spectralPartialQuaternion N T 1 k) atTop (𝓝 1)
    simpa only [spectralPartialQuaternion_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : Quaternion ℝ)) atTop (𝓝 1))
  have hex : ∃ y, Tendsto (spectralPartialQuaternion N T 1) atTop (𝓝 y) := ⟨1, hlim⟩
  unfold spectralQuaternion
  rw [dite_eq_left hex]
  exact tendsto_nhds_unique (Classical.choose_spec hex) hlim

/-- Reflection holds even before proving existence of the full spectral product:
the two defining partial-product sequences agree term by term. -/
theorem spectralQuaternion_one_sub (N : ℕ) (T : H →L[ℂ] H) (q : Quaternion ℝ) :
    spectralQuaternion N T (1 - q) = spectralQuaternion N T q := by
  have hseq : spectralPartialQuaternion N T (1 - q) = spectralPartialQuaternion N T q := by
    funext k
    exact spectralPartialQuaternion_one_sub N T q k
  unfold spectralQuaternion
  rw [hseq]

theorem spectralQuaternion_centered_even (N : ℕ) (T : H →L[ℂ] H) (ξ : Quaternion ℝ) :
    spectralQuaternion N T (1 / 2 + ξ) = spectralQuaternion N T (1 / 2 - ξ) := by
  have : NeZero (2 : Quaternion ℝ) := ⟨by
    intro hzero
    have hh := congrArg (fun q : Quaternion ℝ => q.re) hzero
    change (2 : ℝ) = 0 at hh
    norm_num at hh⟩
  have hq : 1 - (1 / 2 + ξ) = (1 / 2 : Quaternion ℝ) - ξ := by
    rw [sub_add_eq_sub_sub, sub_half]
  simpa only [hq] using (spectralQuaternion_one_sub N T (1 / 2 + ξ)).symm


end SpectralNormalization
end ConditionalGoldbach
