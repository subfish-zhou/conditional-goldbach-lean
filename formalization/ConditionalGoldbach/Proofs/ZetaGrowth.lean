module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import ConditionalGoldbach.Proofs.DensityEulerIdentity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-! Euler summation in the right half-plane and vertical growth estimates. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff LSeries.notation
open MeasureTheory Filter Set Complex Asymptotics
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def zetaFractionKernel (t : ℝ) : ℂ := if 1 < t then ((Int.fract t : ℝ) : ℂ) else 0

def zetaFractionIntegral (s : ℂ) : ℂ := mellin zetaFractionKernel (-s)

lemma zetaFractionKernel_measurable : Measurable zetaFractionKernel := by
  exact (Complex.continuous_ofReal.measurable.comp measurable_fract).ite
    (measurableSet_Ioi) measurable_const

lemma zetaFractionKernel_norm (t : ℝ) : ‖zetaFractionKernel t‖ ≤ 1 := by
  unfold zetaFractionKernel
  split_ifs
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)] using
      (Int.fract_lt_one t).le
  · simp

lemma zetaFractionKernel_local : LocallyIntegrableOn zetaFractionKernel (Ioi 0) := by
  exact ((locallyIntegrable_const (c := (1 : ℂ))).mono
    zetaFractionKernel_measurable.aestronglyMeasurable
    (ae_of_all _ (fun t => by simpa using zetaFractionKernel_norm t))).locallyIntegrableOn _

lemma zetaFractionKernel_top : zetaFractionKernel =O[atTop] (fun t : ℝ => t^(-(0 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards [] with t
  simpa using zetaFractionKernel_norm t

lemma zetaFractionKernel_bottom (b : ℝ) :
    zetaFractionKernel =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply (isBigO_zero _ _).congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [(gt_mem_nhds (show (0 : ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht
  simp [zetaFractionKernel, not_lt.mpr ht.le]

lemma zetaFractionIntegral_regular {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent zetaFractionKernel (-s) ∧ DifferentiableAt ℂ zetaFractionIntegral s := by
  have hbot : -s.re-1 < (-s).re := by simp
  have htop : (-s).re < 0 := by simpa using hs
  refine ⟨mellinConvergent_of_isBigO_rpow zetaFractionKernel_local zetaFractionKernel_top htop
    (zetaFractionKernel_bottom (-s.re-1)) hbot, ?_⟩
  exact DifferentiableAt.comp (g := mellin zetaFractionKernel) (f := fun z : ℂ => -z) s
    (mellin_differentiableAt_of_isBigO_rpow zetaFractionKernel_local zetaFractionKernel_top htop
      (zetaFractionKernel_bottom (-s.re-1)) hbot) (by fun_prop)

lemma zetaFractionIntegral_eq (s : ℂ) : zetaFractionIntegral s =
    ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ)^(-(s+1)) := by
  unfold zetaFractionIntegral mellin
  simp only [smul_eq_mul]
  have he : (fun t : ℝ => (t : ℂ)^(-s-1) * zetaFractionKernel t) =
      (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ)^(-(s+1))) := by
    funext t
    have he : -(s+1) = -s-1 := by ring
    by_cases ht : 1 < t <;> simp [zetaFractionKernel, Set.indicator, ht, he, mul_comm]
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]

lemma zetaFractionIntegral_norm {s : ℂ} (hs : 0 < s.re) :
    ‖zetaFractionIntegral s‖ ≤ 1/s.re := by
  rw [zetaFractionIntegral_eq]
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), ‖((Int.fract t : ℝ) : ℂ)*(t : ℂ)^(-(s+1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1 : ℝ), t^(-s.re-1) := by
      apply integral_mono_ae
      · have hi : IntegrableOn (fun t : ℝ => (t : ℂ)^(-s-1)*zetaFractionKernel t) (Ioi (1 : ℝ)) :=
          (zetaFractionIntegral_regular hs).1.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ)≤1))
        apply hi.norm.congr
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 1 < t at ht
        simp only [zetaFractionKernel]
        rw [ite_eq_left ht]
        congr 1
        rw [show -(s+1) = -s-1 by ring, mul_comm]
      · exact integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) (by norm_num : (0 : ℝ)<1)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change 1 < t at ht
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t),
          Complex.norm_cpow_eq_rpow_re_of_pos (show 0<t by linarith)]
        simp only [neg_re, add_re, one_re]
        calc
          _ ≤ 1 * t^(-(s.re+1)) := mul_le_mul_of_nonneg_right (Int.fract_lt_one t).le (Real.rpow_nonneg (by linarith) _)
          _ = _ := by rw [one_mul]; congr 1; ring
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) (by norm_num : (0 : ℝ)<1)]
      simp

lemma zetaFractionIntegral_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ)^(-(s+1))) (Ioi 1) := by
  have hi : IntegrableOn (fun t : ℝ => (t : ℂ)^(-s-1)*zetaFractionKernel t) (Ioi (1 : ℝ)) :=
    (zetaFractionIntegral_regular hs).1.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ)≤1))
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  change 1<t at ht
  simp only [zetaFractionKernel]
  rw [ite_eq_left ht, show -(s+1) = -s-1 by ring, mul_comm]

lemma riemannZeta_fraction_formula_initial {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s/(s-1) - s*zetaFractionIntegral s := by
  have hsum (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) = n := by simp
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    simp [hsum]
  have he := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hs
    (LSeriesSummable_one_iff.mpr hs) hO
  rw [LSeries_one_eq_riemannZeta hs] at he
  simp only [Pi.one_apply, hsum] at he
  have hp : IntegrableOn (fun t : ℝ => (t : ℂ)^(-s)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) (by norm_num)
  have hf := zetaFractionIntegral_integrable (s := s) (by linarith)
  have hsplit : (∫ t in Ioi (1 : ℝ), (Nat.floor t : ℂ) * (t : ℂ)^(-(s+1))) =
      (∫ t in Ioi (1 : ℝ), (t : ℂ)^(-s)) - zetaFractionIntegral s := by
    rw [zetaFractionIntegral_eq, ← integral_sub hp hf]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    change 1<t at ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hfloor : (Nat.floor t : ℝ) + Int.fract t = t := by
      rw [natCast_floor_eq_intCast_floor (by linarith)]
      exact Int.floor_add_fract t
    have hc := congrArg Complex.ofReal hfloor
    push_cast at hc
    have hpow : (t : ℂ) * (t : ℂ)^(-(s+1)) = (t : ℂ)^(-s) := by
      nth_rw 1 [← Complex.cpow_one (t : ℂ)]
      rw [← Complex.cpow_add _ _ ht0]
      congr 1
      ring
    rw [← hpow]
    linear_combination (t : ℂ)^(-(s+1))*hc
  rw [hsplit, integral_Ioi_cpow_of_lt (by simp; linarith : (-s).re < -1)
    (by norm_num : (0 : ℝ)<1)] at he
  simp only [Complex.ofReal_one, Complex.one_cpow] at he
  rw [show -s+1 = -(s-1) by ring, div_neg, neg_div, neg_neg] at he
  rw [he]
  ring

lemma riemannZeta_fraction_formula {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s/(s-1) - s*zetaFractionIntegral s := by
  let U : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ riemannZeta₁ U := fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hP : DifferentiableOn ℂ zetaFractionIntegral U :=
    fun z hz => (zetaFractionIntegral_regular hz).2.differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => z-z*(z-1)*zetaFractionIntegral z) U := by
    intro z hz
    have hPa := hP.analyticAt (ho.mem_nhds hz)
    exact analyticAt_id.sub ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hPa)
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (2 : ℂ)) (by norm_num [U]) (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ)<(2 : ℂ).re by norm_num)] with z hz
      have hz1 : z ≠ 1 := by intro he; norm_num [he] at hz
      have hf := riemannZeta_fraction_formula_initial hz
      rw [riemannZeta_eq_inv_sub_mul hz1] at hf
      have hn : z-1 ≠ 0 := sub_ne_zero.mpr hz1
      field_simp at hf
      linear_combination hf)
  have hf := heq hs
  rw [riemannZeta_eq_inv_sub_mul hs1, hf]
  field_simp

lemma riemannZeta_vertical_growth {lo M : ℝ} (hlo : 0 < lo) {s : ℂ}
    (hRe : lo ≤ s.re) (hhi : s.re ≤ M) (ht : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (M+1)*(1+1/lo)*(1+|s.im|) := by
  have hs : 0 < s.re := lt_of_lt_of_le hlo hRe
  have hs1 : s ≠ 1 := by
    intro he
    norm_num [he] at ht
  have hn : 1 ≤ ‖s-1‖ := by
    have h := Complex.abs_im_le_norm (s-1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    exact ht.trans h
  have hnorm : ‖s‖ ≤ M+|s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs] at h
    linarith
  have hp : ‖zetaFractionIntegral s‖ ≤ 1/lo :=
    (zetaFractionIntegral_norm hs).trans (one_div_le_one_div_of_le hlo hRe)
  rw [riemannZeta_fraction_formula hs hs1]
  calc
    ‖s/(s-1)-s*zetaFractionIntegral s‖ ≤
        ‖s/(s-1)‖ + ‖s*zetaFractionIntegral s‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + ‖s‖*(1/lo) := by
      rw [norm_div, norm_mul]
      exact add_le_add (div_le_self (norm_nonneg _) hn)
        (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
    _ = ‖s‖*(1+1/lo) := by ring
    _ ≤ (M+|s.im|)*(1+1/lo) :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ (M+1)*(1+1/lo)*(1+|s.im|) := by
      have hM : 0 ≤ M := (le_of_lt hs).trans hhi
      have habs := abs_nonneg s.im
      nlinarith [mul_nonneg hM habs, one_div_pos.mpr hlo]

lemma densityEulerProduct_uniform_bound {lo : ℝ} (hlo : 0 < lo) (N : ℕ)
    {w : ℂ} (hw : lo ≤ w.re) :
    ‖densityEulerProduct N w‖ ≤
      Real.exp (∑' p : ℕ, 3*‖LSeries.term 1 (1+(lo : ℂ)) p‖) := by
  let b : ℕ → ℝ := fun p => 3*‖LSeries.term 1 (1+(lo : ℂ)) p‖
  have hb : Summable b := ((LSeriesSummable_one_iff.mpr (by simpa using hlo)).norm).mul_left 3
  have hm := multipliable_one_add_of_summable
    (densityEulerTerm_summable_norm N (lt_of_lt_of_le hlo hw))
  rw [densityEulerProduct_eq_tprod]
  apply le_of_tendsto hm.hasProd.norm
  filter_upwards [] with S
  calc
    (∏ p ∈ S, ‖1+densityEulerTerm N p w‖) ≤ ∏ p ∈ S, (1+b p) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      calc
        ‖1+densityEulerTerm N p w‖ ≤ 1+‖densityEulerTerm N p w‖ := by
          simpa using norm_add_le (1 : ℂ) (densityEulerTerm N p w)
        _ ≤ 1+b p := add_le_add_right (densityEulerTerm_bound N p lo w hw) 1
    _ ≤ Real.exp (∑ p ∈ S, b p) := Real.prod_one_add_le_exp_sum _ (by intro p; dsimp [b]; positivity)
    _ ≤ Real.exp (∑' p, b p) := Real.exp_le_exp.mpr
      (hb.sum_le_tsum S (by intro p hp; dsimp [b]; positivity))

lemma continuedDensity_vertical_growth (N : ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : lo < hi) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, w.re ∈ Icc lo hi → 1 ≤ |w.im| →
      ‖continuedDensity N w‖ ≤ D*(1+|w.im|) := by
  let A : ℝ := (hi+1)*(1+1/lo)
  let E : ℝ := Real.exp (∑' p : ℕ, 3*‖LSeries.term 1 (1+(lo : ℂ)) p‖)
  have hA : 0 ≤ A := by dsimp [A]; have : 0 < hi := hlo.trans hhi; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hS : 0 ≤ singularSeries N := (singularSeries_pos N).le
  refine ⟨singularSeries N*A*E, by positivity, ?_⟩
  intro w hw ht
  have hζ := riemannZeta_vertical_growth hlo hw.1 hw.2 ht
  have hP := densityEulerProduct_uniform_bound hlo N hw.1
  change ‖(singularSeries N : ℂ)*riemannZeta w*densityEulerProduct N w‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
  calc
    singularSeries N*‖riemannZeta w‖*‖densityEulerProduct N w‖ ≤
        singularSeries N*(A*(1+|w.im|))*E :=
      mul_le_mul (mul_le_mul_of_nonneg_left hζ hS) hP (norm_nonneg _) (by positivity)
    _ = singularSeries N*A*E*(1+|w.im|) := by ring

lemma continuedDensity_uniform_vertical_growth {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : lo < hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Even N → 4 ≤ N →
      ∀ w : ℂ, w.re ∈ Icc lo hi → 1 ≤ |w.im| →
        ‖continuedDensity N w‖ ≤ C*(N : ℝ)/N.totient*(1+|w.im|) := by
  let A : ℝ := (hi+1)*(1+1/lo)
  let E : ℝ := Real.exp (∑' p : ℕ, 3*‖LSeries.term 1 (1+(lo : ℂ)) p‖)
  have hA : 0 < A := by dsimp [A]; have : 0 < hi := hlo.trans hhi; positivity
  have hE : 0 < E := Real.exp_pos _
  refine ⟨A*E, mul_pos hA hE, ?_⟩
  intro N hN hN4 w hw ht
  have hS := (singularSeries_pos N).le
  have hζ := riemannZeta_vertical_growth hlo hw.1 hw.2 ht
  have hP := densityEulerProduct_uniform_bound hlo N hw.1
  change ‖(singularSeries N : ℂ)*riemannZeta w*densityEulerProduct N w‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
  calc
    singularSeries N*‖riemannZeta w‖*‖densityEulerProduct N w‖ ≤
        singularSeries N*(A*(1+|w.im|))*E :=
      mul_le_mul (mul_le_mul_of_nonneg_left hζ hS) hP (norm_nonneg _) (by positivity)
    _ ≤ ((N : ℝ)/N.totient)*(A*(1+|w.im|))*E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (singularSeries_upper_totient N hN (by omega)) (by positivity)) hE.le
    _ = A*E*(N : ℝ)/N.totient*(1+|w.im|) := by ring

end ConditionalGoldbach
