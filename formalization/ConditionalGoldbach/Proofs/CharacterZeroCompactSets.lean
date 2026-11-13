import ConditionalGoldbach.Proofs.CharacterZeroReflection

/-! Compact sets in the multiplicity-indexed zero space and their completed-L exclusion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach

lemma zeroIndex_preimage_compact_finite {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    {K : Set ℂ} (hK : IsCompact K) : ({p : ZeroIndex χ | p.val.1 ∈ K} : Set _).Finite := by
  classical
  let Z : Set ℂ := K ∩ χ.LFunction ⁻¹' {0}
  have hZ : Z.Finite := LFunction_zeros_compact_finite χ hχ hK
  have hB : (⋃ z ∈ Z, ({z} : Set ℂ) ×ˢ Iio (analyticOrderNatAt χ.LFunction z)).Finite :=
    hZ.biUnion (fun z _ => (finite_singleton z).prod (Set.finite_Iio _))
  apply (hB.preimage Subtype.val_injective.injOn).subset
  intro p hp
  simp only [mem_preimage,mem_iUnion,mem_prod,mem_singleton_iff,mem_Iio]
  exact ⟨p.val.1,⟨hp,p.property.2.2.1⟩,rfl,p.property.2.2.2⟩

lemma zeroIndex_bounded_height_finite {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    (T : ℝ) : ({p : ZeroIndex χ | |p.val.1.im| ≤ T} : Set _).Finite := by
  apply (zeroIndex_preimage_compact_finite χ hχ (isCompact_closedBall (0 : ℂ) (T+1))).subset
  intro p hp
  change |p.val.1.im| ≤ T at hp
  apply mem_closedBall_zero_iff.mpr
  have hre : |p.val.1.re| ≤ 1 := by rw [abs_of_pos p.property.1]; exact p.property.2.1.le
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

lemma completedL_zero_at_zeroIndex {d : ℕ} [NeZero d] (χ : Character d) (p : ZeroIndex χ) :
    completedL χ p.val.1 = 0 := by
  have hz := p.property.2.2.1
  have hp0 : p.val.1 ≠ 0 := by
    intro he
    have hh := p.property.1
    rw [he,zero_re] at hh
    linarith
  rw [χ.LFunction_eq_completed_div_gammaFactor p.val.1 (Or.inl hp0)] at hz
  have hC : χ.completedLFunction p.val.1 = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (gammaFactor_ne_zero_re_pos χ p.property.1)
  simp only [completedL,hC,mul_zero]

lemma zeroIndex_ne_of_completedL_ne {d : ℕ} [NeZero d] (χ : Character d) {z : ℂ}
    (hz : completedL χ z ≠ 0) (p : ZeroIndex χ) : z ≠ p.val.1 := by
  intro he
  exact hz (he ▸ completedL_zero_at_zeroIndex χ p)

end ConditionalGoldbach
