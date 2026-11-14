module

public import ConditionalGoldbach.Proofs.LFunctionDomain

/-! Local finiteness of the paper's zeros with multiplicity, using the actual entire L-function. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach

lemma LFunction_zeros_codiscrete {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1) :
    (χ.LFunction ⁻¹' {0})ᶜ ∈ Filter.codiscrete ℂ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction univ := fun z _ =>
    (χ.differentiable_LFunction hχ).analyticAt z
  exact ha.preimage_zero_mem_codiscrete
    (χ.LFunction_ne_zero_of_one_le_re (s := 2) (Or.inl hχ) (by norm_num))

lemma LFunction_zeros_compact_finite {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ χ.LFunction ⁻¹' {0}).Finite := by
  have hc := mem_codiscrete'.mp (LFunction_zeros_codiscrete χ hχ)
  have hclosed : IsClosed (χ.LFunction ⁻¹' {0}) := by simpa using hc.1
  have hdiscrete : IsDiscrete (χ.LFunction ⁻¹' {0}) := by simpa using hc.2
  exact (hK.inter_right hclosed).finite (hdiscrete.mono inter_subset_right)

lemma zeroWindow_finite {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1) (t : ℝ) :
    (zeroWindow χ t).Finite := by
  classical
  let K : Set ℂ := closedBall 0 (|t|+3) ∩ χ.LFunction ⁻¹' {0}
  have hK : K.Finite := LFunction_zeros_compact_finite χ hχ (isCompact_closedBall ..)
  have hB : (⋃ z ∈ K, ({z} : Set ℂ) ×ˢ Set.Iio (analyticOrderNatAt χ.LFunction z)).Finite :=
    hK.biUnion (fun z _ => (finite_singleton z).prod (Set.finite_Iio _))
  apply (hB.preimage Subtype.val_injective.injOn).subset
  intro p hp
  simp only [mem_preimage, mem_iUnion, mem_prod, mem_singleton_iff, mem_Iio]
  refine ⟨p.val.1, ?_, rfl, p.property.2.2.2⟩
  refine ⟨?_, p.property.2.2.1⟩
  apply mem_closedBall_zero_iff.mpr
  have hre : |p.val.1.re| ≤ 1 := by rw [abs_of_pos p.property.1]; exact p.property.2.1.le
  have him : |p.val.1.im| ≤ |t|+1 := by
    apply abs_le.mpr
    have hh := hp
    change t ≤ p.val.1.im ∧ p.val.1.im < t+1 at hh
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

end ConditionalGoldbach
