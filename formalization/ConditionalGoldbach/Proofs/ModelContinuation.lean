module

public import ConditionalGoldbach.Proofs.DensityEuler
public import ConditionalGoldbach.Proofs.BetaIdentity

/-! Continuation of the beta model, with the original two-variable domain. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma gammaQuotient_differentiableAt {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 3 / 2) :
    DifferentiableAt ℂ gammaQuotient s := by
  have ha : 0 < ((3 / 2 - s) / 2).re := by simp; linarith
  have hb : 0 < ((3 / 2 + s) / 2).re := by simp; linarith
  unfold gammaQuotient
  apply DifferentiableAt.div
  · exact (Complex.hasDerivAt_Gamma_of_re_pos ha).differentiableAt.comp s (by fun_prop)
  · exact (Complex.hasDerivAt_Gamma_of_re_pos hb).differentiableAt.comp s (by fun_prop)
  · exact Complex.Gamma_ne_zero_of_re_pos hb

lemma continuedModel_differentiableAt (N : ℕ) (hN : 0 < N) (p : ℂ × ℂ)
    (hp : p ∈ analyticDomain) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ => continuedModel N q.1 q.2) p := by
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs : 0 < (p.1 + p.2).re := by simpa only [add_re] using add_pos hp.1 hp.2.2.1
  have hdD : DifferentiableAt ℂ (densityEulerProduct N) (p.1 + p.2) :=
    (densityEulerProduct_differentiableOn N).differentiableAt (ho.mem_nhds hs)
  have hD : DifferentiableAt ℂ (fun q : ℂ × ℂ => densityEulerProduct N (q.1 + q.2)) p :=
    DifferentiableAt.comp (g := densityEulerProduct N)
      (f := fun q : ℂ × ℂ => q.1 + q.2) p hdD (by fun_prop)
  have hz : 1 - p.1 - p.2 ≠ (1 : ℂ) := by
    intro he
    have hr := congrArg Complex.re he
    simp only [sub_re, one_re] at hr
    simp only [add_re] at hs
    linarith
  have hZ : DifferentiableAt ℂ (fun q : ℂ × ℂ => riemannZeta (1-q.1-q.2)) p :=
    (differentiableAt_riemannZeta hz).comp p (by fun_prop)
  have hG1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => gammaQuotient q.1) p :=
    (gammaQuotient_differentiableAt hp.1 hp.2.1).comp p (by fun_prop)
  have hG2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => gammaQuotient q.2) p :=
    (gammaQuotient_differentiableAt hp.2.2.1 hp.2.2.2).comp p (by fun_prop)
  have hb : (Real.pi : ℂ) / N ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast hN.ne')
  have hP : DifferentiableAt ℂ (fun q : ℂ × ℂ => ((Real.pi : ℂ) / N) ^ (q.1 + q.2)) p :=
    (show DifferentiableAt ℂ (fun q : ℂ × ℂ => q.1 + q.2) p from by fun_prop).const_cpow (Or.inl hb)
  unfold continuedModel
  exact ((((hP.const_mul (singularSeries N : ℂ)).mul hD).mul hZ).mul hG1).mul hG2

lemma continuedModel_differentiableOn (N : ℕ) (hN : 0 < N) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => continuedModel N p.1 p.2) analyticDomain :=
  fun p hp => (continuedModel_differentiableAt N hN p hp).differentiableWithinAt

lemma betaModel_eq_continuedModel (N : ℕ) (hN : 0 < N) (s z : ℂ)
    (hd : (s,z) ∈ betaDomain) : betaModel N s z = continuedModel N s z := by
  have hw0 : 0 < (s+z).re := hd.2.2
  have hw1 : (s+z).re < 1 := by simp only [add_re]; linarith [hd.1, hd.2.1]
  have hneg : ∀ n : ℕ, s+z ≠ -(n : ℂ) := by
    intro n he
    have hr := congrArg Complex.re he
    simp at hr
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [add_re] at hw0
    linarith
  have hne : s+z ≠ (1 : ℂ) := by intro he; simp [he] at hw1
  have hzeta := riemannZeta_one_sub hneg hne
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hpow2 : (2 * Real.pi : ℂ)^(-(s+z)) =
      (2 : ℂ)^(-(s+z)) * (Real.pi : ℂ)^(-(s+z)) := by
    simpa using Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le (-(s+z))
  have hpow : ((Real.pi : ℂ) / N) ^ (s+z) * (2 * Real.pi : ℂ) ^ (-(s+z)) * 2 =
      (N : ℂ)^(-(s+z)) * (2 : ℂ) ^ (1-(s+z)) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
      Complex.div_cpow_ofReal_nonneg Real.pi_pos.le (Nat.cast_nonneg N),
      hpow2,
      Complex.cpow_sub _ _ htwo, Complex.cpow_one]
    simp only [Complex.cpow_neg]
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)]
  unfold betaModel continuedDensity continuedModel
  rw [betaKernel_gamma_identity s z hd,
    show 1-s-z = 1-(s+z) by ring, hzeta]
  linear_combination
    -(singularSeries N : ℂ) * densityEulerProduct N (s+z) * riemannZeta (s+z) *
      Gamma (s+z) * Complex.cos (Real.pi*(s+z)/2) * gammaQuotient s * gammaQuotient z * hpow

theorem proposition_4_4 (N : ℕ) (_hN : Even N) (hN4 : 4 ≤ N) :
    (∀ s z : ℂ, (s, z) ∈ betaDomain → betaModel N s z = continuedModel N s z) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => continuedModel N p.1 p.2) analyticDomain := by
  exact ⟨fun s z hd => betaModel_eq_continuedModel N (by omega) s z hd,
    continuedModel_differentiableOn N (by omega)⟩

end ConditionalGoldbach
