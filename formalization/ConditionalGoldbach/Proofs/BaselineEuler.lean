module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import ConditionalGoldbach.Proofs.DensityResidue

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def baselineEulerTerm (N p : ℕ) (w : ℂ) : ℂ :=
  2*densityEulerTerm N p (1+w)-densityEulerTerm N p (1+2*w)

lemma baselineEulerTerm_eq (N p : ℕ) (w : ℂ) :
    1+baselineEulerTerm N p w = if p.Prime ∧ 2<p ∧ ¬p∣N then
      1+(2*(p:ℂ)^(-w)-(p:ℂ)^(-2*w))/((p:ℂ)*((p:ℂ)-2)) else 1 := by
  unfold baselineEulerTerm densityEulerTerm
  split_ifs with hp
  · have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
    have hp2 : (p:ℂ)-2 ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      have : (2:ℝ)<p := by exact_mod_cast hp.2.1
      linarith
    rw [show -(1+w)=(-1)+(-w) by ring,show -(1+2*w)=(-1)+(-2*w) by ring,
      Complex.cpow_add _ _ hp0,Complex.cpow_add _ _ hp0,Complex.cpow_neg_one]
    field_simp
  · simp

lemma baselineEulerTerm_bound (N p : ℕ) (w : ℂ) (hw : -(1/4:ℝ)<w.re) :
    ‖baselineEulerTerm N p w‖ ≤ 9*‖LSeries.term 1 (3/2:ℂ) p‖ := by
  have h1 := densityEulerTerm_bound N p (1/2) (1+w) (by simp; linarith)
  have h2 := densityEulerTerm_bound N p (1/2) (1+2*w) (by simp; linarith)
  norm_num at h1 h2
  calc
    _ ≤ ‖2*densityEulerTerm N p (1+w)‖+‖densityEulerTerm N p (1+2*w)‖ := norm_sub_le _ _
    _ = 2*‖densityEulerTerm N p (1+w)‖+‖densityEulerTerm N p (1+2*w)‖ := by rw [norm_mul]; norm_num
    _ ≤ _ := by linarith

lemma baselineEulerTerm_differentiable (N p : ℕ) : Differentiable ℂ (baselineEulerTerm N p) := by
  unfold baselineEulerTerm
  apply Differentiable.sub
  · exact ((densityEulerTerm_differentiable N p).comp (by fun_prop)).const_mul 2
  · exact (densityEulerTerm_differentiable N p).comp (by fun_prop)

lemma baselineEulerTerm_summable_norm (N : ℕ) {w : ℂ} (hw : -(1/4:ℝ)<w.re) :
    Summable (fun p => ‖baselineEulerTerm N p w‖) := by
  have hs := ((LSeriesSummable_one_iff.mpr (by norm_num : (1:ℝ)<(3/2:ℂ).re)).norm).mul_left 9
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => baselineEulerTerm_bound N p w hw)

lemma baselineEulerProduct_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (fun w => ∏' p, (1+baselineEulerTerm N p w)) {w : ℂ | -(1/4:ℝ)<w.re} := by
  have ho : IsOpen {w : ℂ | -(1/4:ℝ)<w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs : Summable (fun p => 9*‖LSeries.term 1 (3/2:ℂ) p‖) :=
    ((LSeriesSummable_one_iff.mpr (by norm_num : (1:ℝ)<(3/2:ℂ).re)).norm).mul_left 9
  have hu : TendstoLocallyUniformlyOn
      (fun k w => ∏ p ∈ Finset.range k, (1+baselineEulerTerm N p w))
      (fun w => ∏' p, (1+baselineEulerTerm N p w)) atTop {w : ℂ | -(1/4:ℝ)<w.re} := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact ho).2
    intro K hKU hK
    have hh := hs.hasProdUniformlyOn_nat_one_add hK
      (Eventually.of_forall (fun p w hw => baselineEulerTerm_bound N p w (hKU hw)))
      (fun p => (baselineEulerTerm_differentiable N p).continuous.continuousOn)
    exact hh.tendstoUniformlyOn_finsetRange
  apply hu.differentiableOn _ ho
  filter_upwards with k
  apply Differentiable.differentiableOn
  apply Differentiable.fun_finsetProd
  intro p hp
  exact (differentiable_const (1:ℂ)).add (baselineEulerTerm_differentiable N p)

lemma baselineProductR_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (baselineProductR N) {w : ℂ | -(1/4:ℝ)<w.re} := by
  have he : baselineProductR N = fun w =>
      (∏ p ∈ N.primeFactors, (1-(p:ℂ)^(-1-w)))*(∏' p, (1+baselineEulerTerm N p w)) := by
    funext w
    unfold baselineProductR
    congr 1
    exact (tprod_congr (fun p => baselineEulerTerm_eq N p w)).symm
  rw [he]
  apply DifferentiableOn.mul _ (baselineEulerProduct_differentiableOn N)
  apply Differentiable.differentiableOn
  apply Differentiable.fun_finsetProd
  intro p hp
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  intro w
  exact (differentiableAt_const (c := (1:ℂ))).sub ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -1-w) w).const_cpow (Or.inl hp0))

lemma baselineProductR_zero (N : ℕ) (hN : Even N) (hpos : 0<N) :
    (singularSeries N:ℂ)*baselineProductR N 0=1 := by
  have hp : (∏' p:ℕ, if p.Prime ∧ 2<p ∧ ¬p∣N then
      1+(2*(p:ℂ)^(-(0:ℂ))-(p:ℂ)^(-2*(0:ℂ)))/((p:ℂ)*((p:ℂ)-2)) else 1)=densityEulerProduct N 1 := by
    rw [densityEulerProduct_eq_tprod]
    apply tprod_congr
    intro p
    rw [← baselineEulerTerm_eq]
    simp only [baselineEulerTerm,add_zero,mul_zero]
    ring
  have ht := congrArg Complex.ofReal (totient_ratio_prod N hpos)
  push_cast at ht
  have hfin : (∏ p ∈ N.primeFactors, (1-(p:ℂ)^(-1-(0:ℂ))))*((N:ℂ)/N.totient)=1 := by
    rw [ht,← Finset.prod_mul_distrib]
    have he : ∀ p ∈ N.primeFactors, (1-(p:ℂ)^(-1-(0:ℂ)))*((p:ℂ)/(p-1))=1 := by
      intro p hp
      have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      have hp1 : (p:ℂ)-1 ≠ 0 := by
        intro he
        have hr := congrArg Complex.re he
        simp at hr
        have : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        linarith
      simp only [sub_zero,Complex.cpow_neg_one]
      field_simp
    simp_rw [Finset.prod_congr rfl he,Finset.prod_const_one]
  unfold baselineProductR
  rw [hp]
  calc
    _ = (∏ p ∈ N.primeFactors, (1-(p:ℂ)^(-1-(0:ℂ))))*((singularSeries N:ℂ)*densityEulerProduct N 1) := by ring
    _ = 1 := by rw [singularSeries_mul_densityEuler_one N hN hpos]; exact hfin

theorem proposition_A_4_baseline_product (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε →
      Multipliable (fun p : ℕ => if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
        1 + (2 * (p : ℂ) ^ (-w) - (p : ℂ) ^ (-2 * w)) / ((p : ℂ) * ((p : ℂ) - 2))
        else 1) ∧ DifferentiableAt ℂ (baselineProductR N) w) ∧
    (singularSeries N : ℂ) * baselineProductR N 0 = 1  := by
  refine ⟨⟨1/4,by norm_num,?_⟩,baselineProductR_zero N hN (by omega)⟩
  intro w hw
  have hw' : -(1/4:ℝ)<w.re := by have hh:=Complex.abs_re_le_norm w; have hh' := neg_abs_le w.re; linarith
  constructor
  · convert multipliable_one_add_of_summable (baselineEulerTerm_summable_norm N hw') using 1
    exact funext (fun p => (baselineEulerTerm_eq N p w).symm)
  · exact (baselineProductR_differentiableOn N).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw')

end ConditionalGoldbach
