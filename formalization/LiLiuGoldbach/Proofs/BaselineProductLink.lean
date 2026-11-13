import LiLiuGoldbach.Proofs.BaselineEuler
import LiLiuGoldbach.Proofs.DensityEulerIdentity

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open Set Complex
namespace LiLiuGoldbach16
attribute [local instance] Classical.propDecidable

lemma baselineProduct_factor (N p : ℕ) (hN : Even N) (hpos : 0 < N)
    {w : ℂ} (hw : 0 < w.re) :
    (if p.Prime then (1-(p:ℂ)^(-(1+w)))⁻¹ else 1)*
      (if p∈N.primeFactors then 1-(p:ℂ)^(-1-w) else 1)*
      (1+baselineEulerTerm N p w) = 1+densityEulerTerm N p w := by
  by_cases hp : p.Prime
  · have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hq : ‖(p:ℂ)^(-(1+w))‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re,Complex.add_re,Complex.one_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
    have hqn : 1-(p:ℂ)^(-(1+w)) ≠ 0 := by
      intro he
      have he' : (p:ℂ)^(-(1+w))=1 := by linear_combination -he
      rw [he'] at hq
      simpa only [norm_one,lt_self_iff_false] using hq
    have hm : p∈N.primeFactors ↔ p∣N := by simp [Nat.mem_primeFactors,hp,hpos.ne']
    have he : -1-w=-(1+w) := by ring
    rw [if_pos hp,he]
    by_cases hd : p∣N
    · simp only [if_pos (hm.mpr hd),baselineEulerTerm,densityEulerTerm,hd,not_true_eq_false,
        and_false,ite_false,mul_zero,sub_zero,add_zero,inv_mul_cancel₀ hqn,mul_one]
    · have hp2 : 2<p := by
        have : p≠2 := by intro h; subst p; exact hd (even_iff_two_dvd.mp hN)
        have := hp.two_le
        omega
      rw [if_neg (mt hm.mp hd),mul_one,baselineEulerTerm_eq]
      simp only [hp,hp2,hd,not_false_eq_true,and_self,ite_true,densityEulerTerm]
      have hp2c : (p:ℂ)-2 ≠ 0 := by
        intro h
        have hh := congrArg Complex.re h
        simp at hh
        have hh' : (2:ℝ)<p := by exact_mod_cast hp2
        linarith
      rw [show -(1+w)=(-1)+(-w) by ring,Complex.cpow_add _ _ hp0,Complex.cpow_neg_one]
      have hpow : (p:ℂ)^(-2*w)=((p:ℂ)^(-w))^2 := by
        rw [show -2*w=(-w)+(-w) by ring,Complex.cpow_add _ _ hp0,pow_two]
      rw [hpow]
      have hqn' : 1-(p:ℂ)⁻¹*(p:ℂ)^(-w) ≠ 0 := by
        convert hqn using 1
        rw [show -(1+w)=(-1)+(-w) by ring,Complex.cpow_add _ _ hp0,Complex.cpow_neg_one]
      rw [inv_mul_eq_div,div_eq_iff hqn']
      field_simp
      <;> ring
  · have hm : p∉N.primeFactors := fun h => hp (Nat.prime_of_mem_primeFactors h)
    simp [hp,hm,baselineEulerTerm,densityEulerTerm]

lemma densityEulerProduct_eq_zeta_baseline (N : ℕ) (hN : Even N) (hpos : 0 < N)
    {w : ℂ} (hw : 0 < w.re) :
    densityEulerProduct N w = riemannZeta (1+w)*baselineProductR N w := by
  have hz : HasProd (fun p : ℕ => if p.Prime then (1-(p:ℂ)^(-(1+w)))⁻¹ else 1)
      (riemannZeta (1+w)) := by
    convert ((hasProd_subtype_iff_mulIndicator
      (f := fun p : ℕ => (1-(p:ℂ)^(-(1+w)))⁻¹) (s := {p : ℕ | p.Prime})).mp
      (riemannZeta_eulerProduct_hasProd (by simp; exact hw))) using 1
    ext p
    by_cases hp : p.Prime <;> simp [Set.mulIndicator,hp]
  have hf : HasProd (fun p : ℕ => if p∈N.primeFactors then 1-(p:ℂ)^(-1-w) else 1)
      (∏ p∈N.primeFactors, (1-(p:ℂ)^(-1-w))) := by
    have hh : HasProd (fun p : ℕ => if p∈N.primeFactors then 1-(p:ℂ)^(-1-w) else 1)
        (∏ p∈N.primeFactors, if p∈N.primeFactors then 1-(p:ℂ)^(-1-w) else 1) :=
      hasProd_prod_of_ne_finset_one (fun p hp => ite_eq_right hp)
    simpa only [Finset.prod_ite_of_true (fun p hp => hp)] using hh
  have hb := (multipliable_one_add_of_summable (baselineEulerTerm_summable_norm N (by linarith : -(1/4:ℝ)<w.re))).hasProd
  have he := (multipliable_one_add_of_summable (densityEulerTerm_summable_norm N hw)).hasProd
  rw [← densityEulerProduct_eq_tprod] at he
  have hprod := (hz.mul hf).mul hb
  simp only [baselineProduct_factor N _ hN hpos hw] at hprod
  rw [he.unique hprod]
  unfold baselineProductR
  rw [← mul_assoc]
  congr 1
  exact tprod_congr (fun p => baselineEulerTerm_eq N p w)

end LiLiuGoldbach16
