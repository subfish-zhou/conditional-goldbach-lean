module

public import ConditionalGoldbach.Proofs.DensityEulerIdentity
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-! Uniform arithmetic cancellation in the model kernel. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
open MathlibNt.SieveTheory.SingularSeries hiding singularSeries
attribute [local instance] Classical.propDecidable

lemma model_euler_unramified_bound {p q : ℝ} (hp : 2 < p) (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (p * (p - 2) / (p - 1)^2) * (1 + q / (p - 2)) ≤ (1 - q / p)⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < 1 - q / p := by rw [sub_pos, div_lt_one hp0]; linarith
  rw [inv_eq_one_div, le_div_iff₀ hden]
  have hsq : 0 ≤ (1 - q)^2 := sq_nonneg _
  have he : (p * (p - 2) / (p - 1)^2) * (1 + q / (p - 2)) * (1 - q / p) =
      1 - (1 - q)^2 / (p - 1)^2 := by
    field_simp [show p - 1 ≠ 0 by linarith, show p - 2 ≠ 0 by linarith]; ring
  rw [he]
  exact sub_le_self _ (div_nonneg hsq (sq_nonneg _))

lemma model_euler_ramified_bound {p x : ℝ} (hp : 2 < p) (hx : 1 ≤ x) :
    p / (p - 1) ≤ x * (1 - x⁻¹ / p)⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxi : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).mpr hx
  have hden : 0 < 1 - x⁻¹ / p := by rw [sub_pos, div_lt_one hp0]; linarith
  rw [← div_eq_mul_inv, le_div_iff₀ hden]
  have he : p * (1 - x⁻¹ / p) = p - x⁻¹ := by field_simp
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < p - 1), he]
  have hprod := mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ (p - 1) * x - 1 by nlinarith)
  have : (p - x⁻¹) * x ≤ (x * (p - 1)) * x := by
    rw [sub_mul, inv_mul_cancel₀ hx0.ne']
    nlinarith
  nlinarith

lemma model_zeta_factor_eq (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : 0 < σ) :
    ‖(1 - (p : ℂ)^(-((1 + σ : ℝ) : ℂ)))⁻¹‖ =
      (1 - (p : ℝ)^(-σ) / p)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq : (p : ℝ)^(-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
  have hden : 0 < 1 - (p : ℝ)^(-σ) / p := by
    rw [sub_pos, div_lt_one hp0]
    exact hq.trans_lt hp1
  have he : (p : ℂ)^(-((1 + σ : ℝ) : ℂ)) = (((p : ℝ)^(-σ) / p : ℝ) : ℂ) := by
    rw [show -((1 + σ : ℝ) : ℂ) = ((-(1 + σ) : ℝ) : ℂ) by push_cast; rfl,
      show (p : ℂ) = ((p : ℝ) : ℂ) by simp, ← Complex.ofReal_cpow hp0.le]
    congr 1
    rw [show -(1 + σ) = -σ - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
  rw [he, show (1 : ℂ) = ((1 : ℝ) : ℂ) by rfl, ← Complex.ofReal_sub, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hden]

lemma model_euler_factor_bound (N p : ℕ) (hN : 0 < N) {w : ℂ} (hw : 0 < w.re) :
    ‖((1 + liuBaseDeviation p : ℝ) : ℂ) * (1 + densityEulerTerm N p w) *
      (if p ∈ N.primeFactors.filter (fun p => 2 < p) then (liuCorrectionFactor p : ℂ) else 1)‖ ≤
      (if p ∈ N.primeFactors.filter (fun p => 2 < p) then (p : ℝ)^w.re else 1) *
      ‖if p.Prime then (1 - (p : ℂ)^(-((1 + w.re : ℝ) : ℂ)))⁻¹ else 1‖ := by
  have hb : 0 < 1 + liuBaseDeviation p := one_add_liuBaseDeviation_pos p
  have hmem : p ∈ N.primeFactors.filter (fun p => 2 < p) ↔ p.Prime ∧ 2 < p ∧ p ∣ N := by
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    have hn : N ≠ 0 := hN.ne'
    tauto
  by_cases hp : p.Prime
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    rw [ite_eq_left hp, model_zeta_factor_eq p hp w.re hw]
    by_cases hp2 : 2 < p
    · have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
      have hbase : 1 + liuBaseDeviation p = p * (p - 2) / ((p : ℝ) - 1)^2 := by
        rw [one_add_liuBaseDeviation_eq_baseFactor hp hp2]
        field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]; ring
      have hq0 : 0 ≤ (p : ℝ)^(-w.re) := Real.rpow_nonneg hp0.le _
      have hq1 : (p : ℝ)^(-w.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
      by_cases hpd : p ∣ N
      · have hm := hmem.mpr ⟨hp, hp2, hpd⟩
        simp only [hm, ite_true, densityEulerTerm, hpd, not_true_eq_false, and_false,
          ite_false, add_zero, mul_one]
        rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hb.le (le_of_lt (liuCorrectionFactor_pos hp2))),
          hbase, liuCorrectionFactor]
        have he : p * (p - 2) / ((p : ℝ) - 1)^2 * ((p - 1) / (p - 2)) = p / (p - 1) := by
          field_simp [show (p : ℝ) - 1 ≠ 0 by linarith, show (p : ℝ) - 2 ≠ 0 by linarith]
        rw [he, Real.rpow_neg hp0.le]
        exact model_euler_ramified_bound hp2r (Real.one_le_rpow hp1.le hw.le)
      · have hm : p ∉ N.primeFactors.filter (fun p => 2 < p) := by simp [hmem, hpd]
        simp only [hm, ite_false, mul_one, one_mul]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
        apply (mul_le_mul_of_nonneg_left (norm_add_le 1 (densityEulerTerm N p w)) hb.le).trans
        rw [norm_one, densityEulerTerm, ite_eq_left ⟨hp, hp2, hpd⟩, norm_div,
          Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
        have hd : ‖(p : ℂ) - 2‖ = (p : ℝ) - 2 := by
          rw [show (p : ℂ) - 2 = (((p : ℝ) - 2 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        rw [hd, hbase]
        exact model_euler_unramified_bound hp2r hq0 hq1
    · have hm : p ∉ N.primeFactors.filter (fun p => 2 < p) := by simp [hmem, hp2]
      simp only [hm, ite_false, one_mul, mul_one, liuBaseDeviation, hp2, and_false,
        add_zero, Complex.ofReal_one, densityEulerTerm, false_and, norm_one]
      have hq : (p : ℝ)^(-w.re) / p < 1 := by
        apply (div_lt_one hp0).mpr
        exact (Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)).trans_lt hp1
      exact (one_le_inv₀ (by linarith : 0 < 1 - (p : ℝ)^(-w.re) / p)).mpr (by linarith [div_nonneg (Real.rpow_nonneg hp0.le (-w.re)) hp0.le])
  · have hm : p ∉ N.primeFactors.filter (fun p => 2 < p) := by simp [hmem, hp]
    simp [hm, hp, liuBaseDeviation, densityEulerTerm]

/-- The finite ramified-prime factor is absorbed by the scaling factor `N^σ`. -/
lemma model_primeFactors_rpow_bound (N : ℕ) (hN : 0 < N) (σ : ℝ) (hσ : 0 ≤ σ) :
    (∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (p : ℝ)^σ) ≤ (N : ℝ)^σ := by
  rw [Real.finsetProd_rpow _ _ (fun p hp => Nat.cast_nonneg p)]
  apply Real.rpow_le_rpow (Finset.prod_nonneg (fun p hp => Nat.cast_nonneg p)) _ hσ
  have hd : (∏ p ∈ N.primeFactors.filter (fun p => 2 < p), p) ∣ N :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd N)
  simpa only [Nat.cast_prod] using (Nat.cast_le.mpr (Nat.le_of_dvd hN hd) :
    ((∏ p ∈ N.primeFactors.filter (fun p => 2 < p), p : ℕ) : ℝ) ≤ (N : ℝ))

/-- Exact cancellation of the singular series with the Euler correction yields a bound
independent of `N` once its Mellin scaling has been included. -/
theorem singularSeries_densityEuler_scaled_bound (N : ℕ) (hN : 0 < N)
    {w : ℂ} (hw : 0 < w.re) :
    ‖(N : ℂ)^(-w) * (singularSeries N : ℂ) * densityEulerProduct N w‖ ≤
      2 * ‖riemannZeta ((1 + w.re : ℝ) : ℂ)‖ := by
  let F := N.primeFactors.filter (fun p => 2 < p)
  have he : HasProd (fun p => 1 + densityEulerTerm N p w) (densityEulerProduct N w) := by
    rw [densityEulerProduct_eq_tprod]
    exact (multipliable_one_add_of_summable (densityEulerTerm_summable_norm N hw)).hasProd
  have hb : HasProd (fun p => ((1 + liuBaseDeviation p : ℝ) : ℂ)) (C2 : ℂ) :=
    multipliable_one_add_liuBaseDeviation.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  have hc : HasProd (fun p => if p ∈ F then (liuCorrectionFactor p : ℂ) else 1)
      (liuCorrection N : ℂ) := by
    have hh : HasProd (fun p => if p ∈ F then (liuCorrectionFactor p : ℂ) else 1)
        (∏ p ∈ F, if p ∈ F then (liuCorrectionFactor p : ℂ) else 1) :=
      hasProd_prod_of_ne_finset_one (fun p hp => ite_eq_right hp)
    convert hh using 1
    rw [Finset.prod_ite_of_true (fun p hp => hp)]
    simp only [liuCorrection, Complex.ofReal_prod, F]
  have hx : HasProd (fun p => if p ∈ F then (p : ℝ)^w.re else 1)
      (∏ p ∈ F, (p : ℝ)^w.re) := by
    have hh : HasProd (fun p => if p ∈ F then (p : ℝ)^w.re else 1)
        (∏ p ∈ F, if p ∈ F then (p : ℝ)^w.re else 1) :=
      hasProd_prod_of_ne_finset_one (fun p hp => ite_eq_right hp)
    simpa only [Finset.prod_ite_of_true (fun p hp => hp)] using hh
  have hz : HasProd (fun p : ℕ => if p.Prime then
      (1 - (p : ℂ)^(-((1 + w.re : ℝ) : ℂ)))⁻¹ else 1)
      (riemannZeta ((1 + w.re : ℝ) : ℂ)) := by
    convert ((hasProd_subtype_iff_mulIndicator
      (f := fun p : ℕ => (1 - (p : ℂ)^(-((1 + w.re : ℝ) : ℂ)))⁻¹)
      (s := {p : ℕ | p.Prime})).mp
      (riemannZeta_eulerProduct_hasProd (by simp; linarith : 1 < (((1 + w.re : ℝ) : ℂ)).re))) using 1
    ext p
    by_cases hp : p.Prime <;> simp [Set.mulIndicator, hp]
  have hprod : ‖(C2 : ℂ) * densityEulerProduct N w * (liuCorrection N : ℂ)‖ ≤
      (∏ p ∈ F, (p : ℝ)^w.re) * ‖riemannZeta ((1 + w.re : ℝ) : ℂ)‖ := by
    apply le_of_tendsto_of_tendsto' ((hb.mul he).mul hc).norm (hx.mul hz.norm)
    intro s
    apply Finset.prod_le_prod₀ (fun p hp => norm_nonneg _)
    intro p hp
    exact model_euler_factor_bound N p hN hw
  have hprod' : ‖(C2 : ℂ) * densityEulerProduct N w * (liuCorrection N : ℂ)‖ ≤
      (N : ℝ)^w.re * ‖riemannZeta ((1 + w.re : ℝ) : ℂ)‖ :=
    hprod.trans (mul_le_mul_of_nonneg_right (model_primeFactors_rpow_bound N hN w.re hw.le)
      (norm_nonneg _))
  have hscale : ‖(N : ℂ)^(-w)‖ * (N : ℝ)^w.re = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re,
      Real.rpow_neg (Nat.cast_nonneg _), inv_mul_cancel₀ (Real.rpow_pos_of_pos (by exact_mod_cast hN) _).ne']
  have heq : (N : ℂ)^(-w) * (singularSeries N : ℂ) * densityEulerProduct N w =
      (2 : ℂ) * (N : ℂ)^(-w) * ((C2 : ℂ) * densityEulerProduct N w * (liuCorrection N : ℂ)) := by
    unfold singularSeries liuSingularSeries C2
    push_cast
    ring
  rw [heq, norm_mul, norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 2 * ‖(N : ℂ)^(-w)‖ * ((N : ℝ)^w.re * ‖riemannZeta ((1 + w.re : ℝ) : ℂ)‖) := by
      exact mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = _ := by calc
      _ = 2 * (‖(N : ℂ)^(-w)‖ * (N : ℝ)^w.re) * ‖riemannZeta ((1 + w.re : ℝ) : ℂ)‖ := by ring
      _ = _ := by rw [hscale]; ring

end ConditionalGoldbach
