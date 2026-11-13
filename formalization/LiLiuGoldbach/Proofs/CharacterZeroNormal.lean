import LiLiuGoldbach.Proofs.CharacterZeroSummability
import LiLiuGoldbach.Proofs.CharacterZeroCompactSets

/-! Normal absolute convergence of the paper's paired zero resolvent. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Metric Filter
namespace LiLiuGoldbach16

lemma paired_resolvent_far_bound (R : ℝ) (hR : 1 ≤ R) (u v ρ : ℂ)
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (hρ : 2*R+1 ≤ |ρ.im|) :
    ‖1/(u-ρ)-1/(v-ρ)‖ ≤ 16*R/(1+ρ.im^2) := by
  let y : ℝ := |ρ.im|
  have hy : 1 ≤ y := by dsimp [y]; linarith
  have hρnorm : y ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hu0 : y/2 ≤ ‖u-ρ‖ := by
    have hh := norm_add_le (ρ-u) u
    rw [sub_add_cancel,norm_sub_rev] at hh
    dsimp [y] at *
    linarith
  have hv0 : y/2 ≤ ‖v-ρ‖ := by
    have hh := norm_add_le (ρ-v) v
    rw [sub_add_cancel,norm_sub_rev] at hh
    dsimp [y] at *
    linarith
  have hup : 0 < ‖u-ρ‖ := by linarith
  have hvp : 0 < ‖v-ρ‖ := by linarith
  have hprod : y^2/4 ≤ ‖u-ρ‖*‖v-ρ‖ := by
    have hh := mul_le_mul hu0 hv0 (by positivity : 0 ≤ y/2) (norm_nonneg _)
    nlinarith
  have hnum : ‖v-u‖ ≤ 2*R := (norm_sub_le v u).trans (by linarith)
  have he : 1/(u-ρ)-1/(v-ρ) = (v-u)/((u-ρ)*(v-ρ)) := by
    field_simp [norm_pos_iff.mp hup,norm_pos_iff.mp hvp]
    ring
  rw [he,norm_div,norm_mul]
  apply (div_le_div_iff₀ (mul_pos hup hvp) (by positivity)).mpr
  have hy2 : y^2 = ρ.im^2 := sq_abs _
  calc
    _ ≤ (2*R)*(1+ρ.im^2) := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ (4*R)*y^2 := by nlinarith [sq_nonneg (y-1),mul_nonneg (by linarith : 0≤R) (by nlinarith : 0≤y^2-1)]
    _ ≤ _ := by nlinarith [mul_nonneg (by linarith : 0≤R) (sub_nonneg.mpr hprod)]

lemma primitive_zero_difference_normallySummable {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    NormallySummableOn (fun p : ZeroIndex χ => fun u : ℂ × ℂ =>
      1/(u.1-p.val.1)-1/(u.2-p.val.1))
      {u | completedL χ u.1 ≠ 0 ∧ completedL χ u.2 ≠ 0} := by
  intro K hK hKU
  let F : ZeroIndex χ → (ℂ × ℂ) → ℝ := fun p u => ‖1/(u.1-p.val.1)-1/(u.2-p.val.1)‖
  have hc (p : ZeroIndex χ) : ContinuousOn (F p) K := by
    apply ContinuousOn.norm
    apply ContinuousOn.sub
    · exact continuousOn_const.div (continuous_fst.continuousOn.sub continuousOn_const)
        (fun u hu => sub_ne_zero.mpr (zeroIndex_ne_of_completedL_ne χ (hKU hu).1 p))
    · exact continuousOn_const.div (continuous_snd.continuousOn.sub continuousOn_const)
        (fun u hu => sub_ne_zero.mpr (zeroIndex_ne_of_completedL_ne χ (hKU hu).2 p))
  have he (p : ZeroIndex χ) : {r : ℝ | ∃ u ∈ K, r = F p u} = F p '' K := by
    ext r
    simp only [mem_setOf_eq,mem_image]
    constructor <;> rintro ⟨u,hu,he⟩ <;> exact ⟨u,hu,he.symm⟩
  have hb (p : ZeroIndex χ) : BddAbove {r : ℝ | ∃ u ∈ K, r = F p u} := by
    rw [he]
    exact hK.bddAbove_image (hc p)
  refine ⟨hb,?_⟩
  by_cases hKe : K = ∅
  · simp [hKe]
  have hKn : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R : ℝ := max B 1
  have hR : 1 ≤ R := le_max_right _ _
  have hnorm (u : ℂ × ℂ) (hu : u ∈ K) : ‖u.1‖ ≤ R ∧ ‖u.2‖ ≤ R :=
    ⟨(norm_fst_le u).trans ((hB u hu).trans (le_max_left _ _)),
      (norm_snd_le u).trans ((hB u hu).trans (le_max_left _ _))⟩
  have hs := (primitive_zero_square_summable χ hχ hprim).mul_left (16*R)
  apply hs.of_norm_bounded_eventually
  filter_upwards [(zeroIndex_bounded_height_finite χ hχ (2*R+1)).compl_mem_cofinite] with p hp
  have hfar : 2*R+1 < |p.val.1.im| := lt_of_not_ge hp
  have hnonempty : {r : ℝ | ∃ u ∈ K, r = F p u}.Nonempty := by
    obtain ⟨u,hu⟩ := hKn
    exact ⟨F p u,u,hu,rfl⟩
  have hnonneg : 0 ≤ sSup {r : ℝ | ∃ u ∈ K, r = F p u} := by
    obtain ⟨u,hu⟩ := hKn
    exact (norm_nonneg _).trans (le_csSup (hb p) ⟨u,hu,rfl⟩)
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
  apply csSup_le hnonempty
  rintro r ⟨u,hu,rfl⟩
  simpa only [mul_one_div] using paired_resolvent_far_bound R hR u.1 u.2 p.val.1
    (hnorm u hu).1 (hnorm u hu).2 hfar.le

lemma primitive_zero_difference_summable_norm {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (u v : ℂ)
    (hu : completedL χ u ≠ 0) (hv : completedL χ v ≠ 0) :
    Summable (fun p : ZeroIndex χ => ‖1/(u-p.val.1)-1/(v-p.val.1)‖) := by
  have hh := (primitive_zero_difference_normallySummable χ hχ hprim)
    {(u,v)} (isCompact_singleton) (by intro z hz; rcases mem_singleton_iff.mp hz with rfl; exact ⟨hu,hv⟩)
  simpa using hh.2

end LiLiuGoldbach16
