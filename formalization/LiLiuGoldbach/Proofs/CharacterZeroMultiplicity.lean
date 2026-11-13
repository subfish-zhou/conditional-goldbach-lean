import LiLiuGoldbach.Proofs.CharacterZeroNormal
import LiLiuGoldbach.Proofs.CompletedLZeros

/-! Finite divisor sums agree exactly with the multiplicity-indexed zeros from the paper. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter MeromorphicOn
namespace LiLiuGoldbach16

lemma completed_divisor_eq_orderNat {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    (r : ℝ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) (hz0 : 0 < z.re) :
    divisor (completedL χ) (closedBall (0 : ℂ) r) z = (analyticOrderNatAt χ.LFunction z : ℤ) := by
  rw [divisor_eq_orderNat (fun z _ => (completedL_differentiable χ hχ).analyticAt z) hz]
  simp only [analyticOrderNatAt,completedL_order_eq_LFunction χ hχ hz0]

lemma completed_divisor_support_zero {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (r : ℝ) {z : ℂ}
    (hz : z ∈ (divisor (completedL χ) (closedBall (0 : ℂ) r)).support) :
    0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 := by
  apply (completedL_eq_zero_iff χ hχ hprim z).mp
  by_contra hn
  have hzB := (divisor (completedL χ) (closedBall (0 : ℂ) r)).supportWithinDomain hz
  have ha : AnalyticOnNhd ℂ (completedL χ) (closedBall (0 : ℂ) r) :=
    fun z _ => (completedL_differentiable χ hχ).analyticAt z
  have ho := ((completedL_differentiable χ hχ).analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
  have hd := ha.meromorphicOn.divisor_apply hzB
  rw [ho] at hd
  exact hz (by simpa using hd)

lemma completed_divisor_sum_eq_zeroIndex_sum {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (r : ℝ) (F : ℂ → ℂ) :
    let D := divisor (completedL χ) (closedBall (0 : ℂ) r)
    let hD := D.finiteSupport (isCompact_closedBall ..)
    let hS := zeroIndex_preimage_compact_finite χ hχ (isCompact_closedBall (0 : ℂ) r)
    (∑ z ∈ hD.toFinset, (D z : ℂ)*F z) = ∑ p ∈ hS.toFinset, F p.val.1 := by
  classical
  intro D hD hS
  let S := hS.toFinset
  let Z := hD.toFinset
  have hDzero (p : S) : p.val.val.1 ∈ Z := by
    apply hD.mem_toFinset.mpr
    change D p.val.val.1 ≠ 0
    have hpB : p.val.val.1 ∈ closedBall (0 : ℂ) r := hS.mem_toFinset.mp p.property
    rw [completed_divisor_eq_orderNat χ hχ r hpB p.val.property.1]
    exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) p.val.property.2.2.2))
  have hZdata (z : Z) : 0 < z.val.re ∧ z.val.re < 1 ∧ χ.LFunction z.val = 0 :=
    completed_divisor_support_zero χ hχ hprim r (hD.mem_toFinset.mp z.property)
  have hZB (z : Z) : z.val ∈ closedBall (0 : ℂ) r := D.supportWithinDomain (hD.mem_toFinset.mp z.property)
  let e : S ≃ (Σ z : Z, Fin (analyticOrderNatAt χ.LFunction z.val)) :=
    { toFun := fun p => ⟨⟨p.val.val.1,hDzero p⟩,⟨p.val.val.2,p.val.property.2.2.2⟩⟩
      invFun := fun q => ⟨⟨(q.1.val,q.2.val),⟨(hZdata q.1).1,(hZdata q.1).2.1,(hZdata q.1).2.2,q.2.isLt⟩⟩,
        hS.mem_toFinset.mpr (hZB q.1)⟩
      left_inv := fun p => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun q => by cases q; rfl }
  have he := Fintype.sum_equiv e (fun p : S => F p.val.val.1)
    (fun q : (Σ z : Z, Fin (analyticOrderNatAt χ.LFunction z.val)) => F q.1.val) (fun _ => rfl)
  rw [Fintype.sum_sigma] at he
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  rw [Finset.sum_coe_sort S (fun p : ZeroIndex χ => F p.val.1)] at he
  have hcast : (∑ z : Z, (analyticOrderNatAt χ.LFunction z.val : ℂ)*F z.val) =
      ∑ z ∈ hD.toFinset, (D z : ℂ)*F z := by
    have hterm (z : Z) : (analyticOrderNatAt χ.LFunction z.val : ℂ)*F z.val = (D z.val : ℂ)*F z.val := by
      rw [completed_divisor_eq_orderNat χ hχ r (hZB z) (hZdata z).1]
      norm_cast
    simp_rw [hterm]
    exact Finset.sum_coe_sort Z (fun z : ℂ => (D z : ℂ)*F z)
  exact hcast.symm.trans he.symm

end LiLiuGoldbach16
