import LiLiuGoldbach.Proofs.DensityEuler
import LiLiuGoldbach.Proofs.SingularBounds

/-! Exact Euler-factor cancellation at one and the density residue. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
open MathlibNt.SieveTheory.SingularSeries hiding singularSeries
attribute [local instance] Classical.propDecidable

lemma densityEuler_factor_at_one (N p : ℕ) (hN : 0 < N) :
    (1 + densityEulerTerm N p 1) * ((1 + liuBaseDeviation p : ℝ) : ℂ) =
      if p ∈ N.primeFactors.filter (fun p => 2 < p) then
        ((1 + liuBaseDeviation p : ℝ) : ℂ) else 1 := by
  by_cases hp : p.Prime ∧ 2 < p
  · have hp2 : (2 : ℝ) < p := by exact_mod_cast hp.2
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hpm1 : (p : ℂ) - 1 ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    have hpm2 : (p : ℂ) - 2 ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    by_cases hpd : p ∣ N
    · simp [densityEulerTerm, hp.1, hp.2, hpd, Nat.mem_primeFactors, hN.ne']
    · simp only [densityEulerTerm, hp.1, hp.2, hpd, not_false_eq_true, and_self,
        ite_true, Complex.cpow_neg, Complex.cpow_one]
      rw [ite_eq_right (by simp [Finset.mem_filter, Nat.mem_primeFactors, hpd]),
        one_add_liuBaseDeviation_eq_baseFactor hp.1 hp.2]
      push_cast
      field_simp
      ring
  · have hpm : p ∉ N.primeFactors.filter (fun p => 2 < p) := by
      intro hm
      exact hp ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hm).1,
        (Finset.mem_filter.mp hm).2⟩
    simp only [densityEulerTerm, liuBaseDeviation, hp, ite_false, add_zero, Complex.ofReal_one,
      hpm, one_mul]
    rw [ite_eq_right (by tauto)]
    norm_num

lemma densityEuler_at_one_mul_C2 (N : ℕ) (hN : 0 < N) :
    densityEulerProduct N 1 * (C2 : ℂ) =
      ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), ((1 + liuBaseDeviation p : ℝ) : ℂ) := by
  have he : HasProd (fun p => 1 + densityEulerTerm N p 1) (densityEulerProduct N 1) := by
    rw [densityEulerProduct_eq_tprod]
    exact (multipliable_one_add_of_summable (densityEulerTerm_summable_norm N (by norm_num))).hasProd
  have hb : HasProd (fun p => ((1 + liuBaseDeviation p : ℝ) : ℂ)) (C2 : ℂ) :=
    multipliable_one_add_liuBaseDeviation.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  have hp := he.mul hb
  have heq := hp.tprod_eq
  rw [← heq]
  simp_rw [densityEuler_factor_at_one N _ hN]
  rw [tprod_eq_prod (s := N.primeFactors.filter (fun p => 2 < p))
    (fun p hp => ite_eq_right hp)]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [hp, ite_true]

lemma singularSeries_mul_densityEuler_one (N : ℕ) (hN : Even N) (hpos : 0 < N) :
    (singularSeries N : ℂ) * densityEulerProduct N 1 = (N : ℂ)/N.totient := by
  have he : liuCorrection N *
      (∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + liuBaseDeviation p)) =
      ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (p : ℝ)/(p-1) := by
    unfold liuCorrection
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 := (Finset.mem_filter.mp hp).2
    have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    rw [one_add_liuBaseDeviation_eq_baseFactor hprime hp2, liuCorrectionFactor,
      ← liuLocalFactor_of_dvd hp2 (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
    simp [liuLocalFactor, Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1]
  have hreal : 2 * (liuCorrection N *
      (∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + liuBaseDeviation p))) =
      (N : ℝ)/N.totient := by rw [he, totient_ratio_odd_prod N hN hpos]
  have heuler := densityEuler_at_one_mul_C2 N hpos
  unfold singularSeries liuSingularSeries
  push_cast
  calc
    _ = 2 * (liuCorrection N : ℂ) * (densityEulerProduct N 1 * (C2 : ℂ)) := by dsimp only [C2]; ring
    _ = _ := by
      rw [heuler]
      have hc := congrArg Complex.ofReal hreal
      push_cast at hc
      simpa only [mul_assoc, Complex.ofReal_add, Complex.ofReal_one] using hc

lemma continuedDensity_residue_one (N : ℕ) (hN : Even N) (hpos : 0 < N) :
    Tendsto (fun w : ℂ => (w-1)*continuedDensity N w) (𝓝[≠] 1)
      (𝓝 ((N : ℂ)/N.totient)) := by
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : ContinuousAt (densityEulerProduct N) 1 :=
    ((densityEulerProduct_differentiableOn N).differentiableAt
      (ho.mem_nhds (by norm_num))).continuousAt
  have h := (riemannZeta_residue_one.mul hd.continuousWithinAt.tendsto).const_mul (singularSeries N : ℂ)
  simp only [one_mul, singularSeries_mul_densityEuler_one N hN hpos] at h
  convert h using 1
  funext w
  unfold continuedDensity
  ring

lemma riemannZeta_meromorphicAt_re_pos {w : ℂ} (hw : 0 < w.re) :
    MeromorphicAt riemannZeta w := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓ : AnalyticAt ℂ Gamma (w/2) :=
    (show DifferentiableOn ℂ Gamma {z | 0 < z.re} from
      fun z hz => (Complex.hasDerivAt_Gamma_of_re_pos hz).differentiableAt.differentiableWithinAt).analyticAt
      (ho.mem_nhds (by simp; linarith))
  have hG : AnalyticAt ℂ (fun z : ℂ => Gamma (z/2)) w := AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z/2) hΓ (by fun_prop)
  have hP : Differentiable ℂ (fun z : ℂ => (Real.pi : ℂ)^(-z/2)) := by
    intro z
    exact (show DifferentiableAt ℂ (fun z : ℂ => -z/2) z from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hm : MeromorphicAt (fun z : ℂ =>
      (completedRiemannZeta₀ z - 1/z - 1/(1-z)) /
        ((Real.pi : ℂ)^(-z/2) * Gamma (z/2))) w := by
    apply MeromorphicAt.div
    · apply MeromorphicAt.sub
      · exact (differentiable_completedZeta₀.analyticAt w).meromorphicAt.sub
          ((MeromorphicAt.const 1 w).div (analyticAt_id.meromorphicAt))
      · exact (MeromorphicAt.const 1 w).div
          ((show AnalyticAt ℂ (fun z : ℂ => 1-z) w from by fun_prop).meromorphicAt)
    · exact ((hP.analyticAt w).mul hG).meromorphicAt
  apply hm.congr
  have hn : w ≠ 0 := by intro he; simp [he] at hw
  have he : ∀ᶠ z in 𝓝 w, z ≠ (0 : ℂ) := eventually_ne_nhds hn
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
  exact (riemannZeta_eq_completedRiemannZeta₀ hz).symm

lemma continuedDensity_meromorphicOn (N : ℕ) :
    MeromorphicOn (continuedDensity N) {w | 0 < w.re} := by
  intro w hw
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableAt ℂ (densityEulerProduct N) w :=
    (densityEulerProduct_differentiableOn N).differentiableAt (ho.mem_nhds hw)
  exact ((MeromorphicAt.const (singularSeries N : ℂ) w).mul
    (riemannZeta_meromorphicAt_re_pos hw)).mul
      ((densityEulerProduct_differentiableOn N).analyticAt (ho.mem_nhds hw)).meromorphicAt

lemma continuedDensity_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (continuedDensity N) {w | 0 < w.re ∧ w ≠ 1} := by
  intro w hw
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableAt ℂ (densityEulerProduct N) w :=
    (densityEulerProduct_differentiableOn N).differentiableAt (ho.mem_nhds hw.1)
  exact (((differentiableAt_riemannZeta hw.2).const_mul (singularSeries N : ℂ)).mul hD).differentiableWithinAt

end LiLiuGoldbach16
