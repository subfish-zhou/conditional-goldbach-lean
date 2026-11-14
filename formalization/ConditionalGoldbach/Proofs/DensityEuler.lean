module

public import ConditionalGoldbach.Definitions.Asymptotics
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import ConditionalGoldbach.Proofs.DensitySeries

/-! Normal convergence of the density Euler correction in the full right half-plane. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

def densityEulerTerm (N p : ℕ) (w : ℂ) : ℂ :=
  if p.Prime ∧ 2 < p ∧ ¬p ∣ N then (p : ℂ)^(-w) / ((p : ℂ)-2) else 0

lemma densityEulerTerm_bound (N p : ℕ) (δ : ℝ) (w : ℂ) (hw : δ ≤ w.re) :
    ‖densityEulerTerm N p w‖ ≤ 3 * ‖LSeries.term 1 (1 + (δ : ℂ)) p‖ := by
  unfold densityEulerTerm
  split_ifs with hp
  · have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hp2 : (2 : ℝ) < p := by exact_mod_cast hp.2.1
    have hpden : (p : ℂ) - 2 ≠ 0 := by
      intro he
      have he' := congrArg Complex.re he
      simp at he'
      linarith
    have heq : (p : ℂ)^(-w) / ((p : ℂ)-2) =
        ((p : ℂ) / ((p : ℂ)-2)) * LSeries.term 1 (1+w) p := by
      rw [LSeries.term_of_ne_zero (show p ≠ 0 by omega)]
      simp only [Pi.one_apply, Complex.cpow_add _ _ hp0, Complex.cpow_one,
        Complex.cpow_neg, div_eq_mul_inv]
      field_simp
    rw [heq, norm_mul]
    have hr : ‖(p : ℂ) / ((p : ℂ)-2)‖ ≤ 3 := by
      rw [norm_div, Complex.norm_natCast]
      have he : ‖(p : ℂ) - 2‖ = (p : ℝ) - 2 := by
        rw [show (p : ℂ) - 2 = (((p : ℝ) - 2 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [he, div_le_iff₀ (by linarith)]
      have : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      linarith
    exact mul_le_mul hr (LSeries.norm_term_le_of_re_le_re 1 (by simpa using hw) p)
      (norm_nonneg _) (by norm_num)
  · simp

lemma densityEulerTerm_continuous (N p : ℕ) : Continuous (densityEulerTerm N p) := by
  unfold densityEulerTerm
  split_ifs with hp
  · have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    exact (continuous_neg.const_cpow (Or.inl hp0)).div_const _
  · fun_prop

lemma densityEulerTerm_differentiable (N p : ℕ) : Differentiable ℂ (densityEulerTerm N p) := by
  unfold densityEulerTerm
  split_ifs with hp
  · have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    intro w
    exact ((differentiableAt_id.neg.const_cpow (Or.inl hp0))).div_const _
  · fun_prop

lemma densityEuler_compact_majorant (N : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ {w | 0 < w.re}) :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ p w, w ∈ K → ‖densityEulerTerm N p w‖ ≤ b p := by
  by_cases hne : K.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
    refine ⟨fun p => 3 * ‖LSeries.term 1 (1 + (w₀.re : ℂ)) p‖,
      ?_, fun p w hw => densityEulerTerm_bound N p w₀.re w (hmin hw)⟩
    apply Summable.mul_left
    exact (LSeriesSummable_one_iff.mpr (by simpa using hKU hw₀)).norm
  · refine ⟨0, summable_zero, ?_⟩
    intro p w hw
    exact (hne ⟨w, hw⟩).elim

lemma normallySummableOn_of_compact_majorant {ι X : Type*} [TopologicalSpace X]
    (f : ι → X → ℂ) (U : Set X)
    (h : ∀ K : Set X, IsCompact K → K ⊆ U →
      ∃ b : ι → ℝ, Summable b ∧ ∀ i x, x ∈ K → ‖f i x‖ ≤ b i) :
    NormallySummableOn f U := by
  intro K hK hKU
  obtain ⟨b, hb, hbound⟩ := h K hK hKU
  have hB (i : ι) : BddAbove {r : ℝ | ∃ x ∈ K, r = ‖f i x‖} := by
    refine ⟨b i, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact hbound i x hx
  refine ⟨hB, ?_⟩
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx⟩ := hne
    apply hb.of_nonneg_of_le
    · intro i
      exact (norm_nonneg _).trans (le_csSup (hB i) ⟨x, hx, rfl⟩)
    · intro i
      exact csSup_le ⟨‖f i x‖, x, hx, rfl⟩ (by
        rintro r ⟨y, hy, rfl⟩
        exact hbound i y hy)
  · have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [he]

lemma densityEulerTerm_normallySummable (N : ℕ) :
    NormallySummableOn (densityEulerTerm N) {w | 0 < w.re} :=
  normallySummableOn_of_compact_majorant _ _ (densityEuler_compact_majorant N)

lemma densityEulerProduct_eq_tprod (N : ℕ) (w : ℂ) :
    densityEulerProduct N w = ∏' p : ℕ, (1 + densityEulerTerm N p w) := by
  apply tprod_congr
  intro p
  unfold densityEulerTerm
  split_ifs <;> simp

lemma densityEulerTerm_summable_norm (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Summable (fun p => ‖densityEulerTerm N p w‖) := by
  have hb : Summable (fun p => 3 * ‖LSeries.term 1 (1 + (w.re : ℂ)) p‖) :=
    ((LSeriesSummable_one_iff.mpr (by simpa using hw)).norm).mul_left 3
  exact hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => densityEulerTerm_bound N p w.re w le_rfl)

lemma densityEulerProduct_multipliable (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Multipliable (fun p : ℕ => if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
      1 + (p : ℂ)^(-w) / ((p : ℂ)-2) else 1) := by
  convert multipliable_one_add_of_summable (densityEulerTerm_summable_norm N hw) using 1
  ext p
  unfold densityEulerTerm
  split_ifs <;> simp

lemma densityEulerProduct_hasProdUniformlyOn (N : ℕ) (K : Set ℂ)
    (hK : IsCompact K) (hKU : K ⊆ {w | 0 < w.re}) :
    HasProdUniformlyOn (fun p w => 1 + densityEulerTerm N p w) (densityEulerProduct N) K := by
  obtain ⟨b, hb, hbound⟩ := densityEuler_compact_majorant N K hK hKU
  have hu := hb.hasProdUniformlyOn_nat_one_add hK
    (Filter.Eventually.of_forall hbound)
    (fun p => (densityEulerTerm_continuous N p).continuousOn)
  simpa only [← densityEulerProduct_eq_tprod] using hu

lemma densityEulerProduct_differentiableOn (N : ℕ) :
    DifferentiableOn ℂ (densityEulerProduct N) {w | 0 < w.re} := by
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hu : TendstoLocallyUniformlyOn
      (fun k w => ∏ p ∈ Finset.range k, (1 + densityEulerTerm N p w))
      (densityEulerProduct N) atTop {w | 0 < w.re} := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact ho).2
    intro K hKU hK
    exact (densityEulerProduct_hasProdUniformlyOn N K hK hKU).tendstoUniformlyOn_finsetRange
  apply hu.differentiableOn _ ho
  filter_upwards with k
  apply Differentiable.differentiableOn
  apply Differentiable.fun_finsetProd
  intro p hp
  exact (differentiable_const (1 : ℂ)).add (densityEulerTerm_differentiable N p)

theorem lemma_4_3_euler_product_convergence (N : ℕ) (_hN : Even N) (_hN4 : 4 ≤ N) :
    NormallySummableOn (fun p : ℕ => fun w : ℂ =>
      if p.Prime ∧ 2 < p ∧ ¬p ∣ N then (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 0)
      {w | 0 < w.re} ∧
    (∀ w : ℂ, 0 < w.re → Multipliable (fun p : ℕ =>
      if p.Prime ∧ 2 < p ∧ ¬p ∣ N then
        1 + (p : ℂ) ^ (-w) / ((p : ℂ) - 2) else 1)) ∧
    DifferentiableOn ℂ (densityEulerProduct N) {w | 0 < w.re} ∧
    DifferentiableOn ℂ (diagonalSeries N) {w | 0 < w.re} := by
  exact ⟨densityEulerTerm_normallySummable N,
    fun w hw => densityEulerProduct_multipliable N hw,
    densityEulerProduct_differentiableOn N, diagonalSeries_differentiableOn N⟩

end ConditionalGoldbach
