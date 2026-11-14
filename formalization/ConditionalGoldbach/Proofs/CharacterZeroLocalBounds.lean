module

public import ConditionalGoldbach.Proofs.CharacterZeroCounting
public import ConditionalGoldbach.Proofs.CharacterZeroReflection

/-! Uniform, unconditional local zero counting, including multiplicities and both half-strips. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach

lemma zeroClosedWindow_finite {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1) (t : ℝ) :
    ({p : ZeroIndex χ | t ≤ p.val.1.im ∧ p.val.1.im ≤ t+1} : Set _).Finite := by
  apply ((zeroWindow_finite χ hχ t).union (zeroWindow_finite χ hχ (t+1))).subset
  intro p hp
  by_cases hh : p.val.1.im < t+1
  · exact Or.inl ⟨hp.1,hh⟩
  · exact Or.inr ⟨le_of_not_gt hh,by linarith [hp.2]⟩

lemma zeroWindow_count_le_right_counts {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℝ) :
    (zeroWindow χ t).ncard ≤
      ({p : ZeroIndex χ | 1/2 ≤ p.val.1.re ∧ t ≤ p.val.1.im ∧ p.val.1.im ≤ t+1} : Set _).ncard +
      ({p : ZeroIndex χ⁻¹ | 1/2 ≤ p.val.1.re ∧ -t-1 ≤ p.val.1.im ∧ p.val.1.im ≤ -t} : Set _).ncard := by
  let R : Set (ZeroIndex χ) := {p | 1/2 ≤ p.val.1.re ∧ t ≤ p.val.1.im ∧ p.val.1.im ≤ t+1}
  let L : Set (ZeroIndex χ) := {p | p ∈ zeroWindow χ t ∧ p.val.1.re < 1/2}
  let R' : Set (ZeroIndex χ⁻¹) := {p | 1/2 ≤ p.val.1.re ∧ -t-1 ≤ p.val.1.im ∧ p.val.1.im ≤ -t}
  have hR : R.Finite := (zeroClosedWindow_finite χ hχ t).subset (fun _ h => h.2)
  have hL : L.Finite := (zeroWindow_finite χ hχ t).subset (fun _ h => h.1)
  have hR' : R'.Finite := (zeroClosedWindow_finite χ⁻¹ (inv_ne_one.mpr hχ) (-t-1)).subset (by
    intro p hp
    exact ⟨hp.2.1,by linarith [hp.2.2]⟩)
  have hcover : zeroWindow χ t ⊆ R ∪ L := by
    intro p hp
    by_cases hr : 1/2 ≤ p.val.1.re
    · exact Or.inl ⟨hr,hp.1,hp.2.le⟩
    · exact Or.inr ⟨hp,lt_of_not_ge hr⟩
  have hcardL : L.ncard ≤ R'.ncard := by
    apply Set.ncard_le_ncard_of_injOn (reflectedZero χ hχ hprim) _
      (reflectedZero_injective χ hχ hprim).injOn hR'
    intro p hp
    change 1/2 ≤ (1-p.val.1).re ∧ -t-1 ≤ (1-p.val.1).im ∧ (1-p.val.1).im ≤ -t
    simp only [sub_re,sub_im,one_re,one_im,zero_sub]
    exact ⟨by linarith [hp.2],by linarith [hp.1.2],by linarith [hp.1.1]⟩
  exact (Set.ncard_le_ncard hcover (hR.union hL)).trans
    ((Set.ncard_union_le R L).trans (Nat.add_le_add_left hcardL _))

lemma logarithm_zero_count_bound (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    Real.log (39*(d : ℝ)*(|t|+2)) ≤ 79*Real.log ((d : ℝ)*(|t|+2)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let X : ℝ := (d : ℝ)*(|t|+2)
  have hX : 2 ≤ X := by dsimp [X]; nlinarith [abs_nonneg t]
  have hXp : 0 < X := by linarith
  have hlog : (1/2 : ℝ) ≤ Real.log X := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    have hxlog := Real.log_le_log (by norm_num : (0 : ℝ)<2) hX
    norm_num at hh
    linarith
  have he : 39*(d : ℝ)*(|t|+2) = 39*X := by dsimp [X]; ring
  rw [he,Real.log_mul (by norm_num : (39 : ℝ)≠0) hXp.ne']
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<39)
  change Real.log 39+Real.log X ≤ 79*Real.log X
  linarith

theorem primitive_local_zero_count : ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, ∀ (_ : NeZero d), ∀ χ : Character d,
      χ ≠ 1 → χ.IsPrimitive → ∀ t : ℝ,
        (zeroWindow χ t).Finite ∧
        ((zeroWindow χ t).ncard : ℝ) ≤ C*Real.log (d*(|t|+2)) := by
  let D : ℝ := Real.log ((11/4 : ℝ)/(8/3))
  have hD : 0 < D := Real.log_pos (by norm_num)
  refine ⟨158/D, by positivity, fun d _ χ hχ hprim t => ⟨zeroWindow_finite χ hχ t,?_⟩⟩
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hright := LFunction_zero_count_right_half_closed χ hχ t
  have hleft := LFunction_zero_count_right_half_closed χ⁻¹ (inv_ne_one.mpr hχ) (-t-1)
  have hsum := zeroWindow_count_le_right_counts χ hχ hprim t
  have hleft' : (({p : ZeroIndex χ⁻¹ | 1/2 ≤ p.val.1.re ∧ -t-1 ≤ p.val.1.im ∧ p.val.1.im ≤ -t} : Set _).ncard : ℝ) ≤
      Real.log (26*(d : ℝ)*(|-t-1|+2))/D := by
    convert hleft using 2; congr 3; ring_nf
  have hlog := logarithm_zero_count_bound d hd t
  have hr : Real.log (26*(d : ℝ)*(|t|+2)) ≤ 79*Real.log ((d : ℝ)*(|t|+2)) := by
    apply (Real.log_le_log (by positivity) _).trans hlog
    nlinarith [abs_nonneg t]
  have hl : Real.log (26*(d : ℝ)*(|-t-1|+2)) ≤ 79*Real.log ((d : ℝ)*(|t|+2)) := by
    apply (Real.log_le_log (by positivity) _).trans hlog
    have hh : |-t-1| ≤ |t|+1 := by
      simpa only [sub_eq_add_neg,abs_neg,abs_one] using abs_add_le (-t) (-1 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hh (by linarith : (0 : ℝ)≤d),abs_nonneg t]
  have hright' := hright.trans (div_le_div_of_nonneg_right hr hD.le)
  have hleft'' := hleft'.trans (div_le_div_of_nonneg_right hl hD.le)
  have hsumR : ((zeroWindow χ t).ncard : ℝ) ≤
      (({p : ZeroIndex χ | 1/2 ≤ p.val.1.re ∧ t ≤ p.val.1.im ∧ p.val.1.im ≤ t+1} : Set _).ncard : ℝ) +
      (({p : ZeroIndex χ⁻¹ | 1/2 ≤ p.val.1.re ∧ -t-1 ≤ p.val.1.im ∧ p.val.1.im ≤ -t} : Set _).ncard : ℝ) := by
    exact_mod_cast hsum
  calc
    _ ≤ 79*Real.log ((d : ℝ)*(|t|+2))/D + 79*Real.log ((d : ℝ)*(|t|+2))/D :=
      hsumR.trans (add_le_add hright' hleft'')
    _ = _ := by ring

end ConditionalGoldbach
