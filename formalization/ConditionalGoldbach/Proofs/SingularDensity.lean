module

public import ConditionalGoldbach.Definitions.Arithmetic
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Exact local factors and arithmetic bounds for the source singular series. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma localDensityFactor_eq_liu {p h : ℕ} (hp : 2 < p) :
    localDensityFactor p h = MathlibNt.SieveTheory.SingularSeries.liuLocalFactor p h := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold localDensityFactor MathlibNt.SieveTheory.SingularSeries.liuLocalFactor
  split_ifs <;> field_simp

lemma localDensityFactor_two {h : ℕ} (hh : Even h) : localDensityFactor 2 h = 2 := by
  norm_num [localDensityFactor, hh.two_dvd]

lemma localDensityFactor_factorization (h : ℕ) (hh : Even h) (hpos : 0 < h) (p : ℕ) :
    (if p.Prime then localDensityFactor p h else 1) =
      (if p = 2 then (2 : ℝ) else 1) *
        (if p ∈ h.primeFactors.filter (fun p => 2 < p) then MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor p else 1) *
          (1 + MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation p) := by
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      simp [localDensityFactor_two hh, MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation, Nat.prime_two]
    · have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
      rw [ite_eq_left hp, localDensityFactor_eq_liu hpgt,
        MathlibNt.SieveTheory.SingularSeries.liuLocalFactor_eq_correction_mul_base hp hpgt, ite_eq_right hp2, one_mul]
      simp [Finset.mem_filter, Nat.mem_primeFactors, hp, hpgt, hpos.ne']
  · have hp2 : p ≠ 2 := by rintro rfl; exact hp Nat.prime_two
    have hpm : p ∉ h.primeFactors.filter (fun p => 2 < p) := by
      intro hm
      exact hp (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hm).1)
    simp [hp, hp2, hpm, MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation]

lemma localDensity_hasProd (h : ℕ) (hh : Even h) (hpos : 0 < h) :
    HasProd (fun p : ℕ => if p.Prime then localDensityFactor p h else 1) (singularSeries h) := by
  have hc : HasProd
      (fun p : ℕ => if p ∈ h.primeFactors.filter (fun p => 2 < p) then MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor p else 1)
      (MathlibNt.SieveTheory.SingularSeries.liuCorrection h) := by
    convert hasProd_prod_of_ne_finset_one
      (s := h.primeFactors.filter (fun p => 2 < p))
      (f := fun p => if p ∈ h.primeFactors.filter (fun p => 2 < p) then MathlibNt.SieveTheory.SingularSeries.liuCorrectionFactor p else 1)
      (fun p hp => ite_eq_right hp) using 1
    · unfold MathlibNt.SieveTheory.SingularSeries.liuCorrection
      apply Finset.prod_congr rfl
      intro p hp
      simp only [hp, ite_true]
    · infer_instance
  have hb : HasProd (fun p : ℕ => 1 + MathlibNt.SieveTheory.SingularSeries.liuBaseDeviation p) MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct :=
    MathlibNt.SieveTheory.SingularSeries.multipliable_one_add_liuBaseDeviation.hasProd
  have ht := ((hasProd_ite_eq (2 : ℕ) (2 : ℝ)).mul hc).mul hb
  convert ht using 1
  · ext p
    exact localDensityFactor_factorization h hh hpos p
  · simp [singularSeries, MathlibNt.SieveTheory.SingularSeries.liuSingularSeries, mul_assoc]

theorem lemma_4_1_local_density (h : ℕ) (hh : Even h) (hpos : 0 < h) :
    (∏' p : ℕ, if p.Prime then localDensityFactor p h else 1) = singularSeries h :=
  (localDensity_hasProd h hh hpos).tprod_eq

end ConditionalGoldbach
