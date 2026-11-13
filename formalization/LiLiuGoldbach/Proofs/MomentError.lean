import LiLiuGoldbach.Proofs.WideMoments

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LiLiuGoldbach16

lemma norm_square_difference_le (z w : ℂ) :
    |‖z‖^2-‖w‖^2| ≤ 2*‖w‖*‖z-w‖+‖z-w‖^2 := by
  have hdiff := abs_norm_sub_norm_le z w
  have htri : ‖z‖ ≤ ‖w‖+‖z-w‖ := by
    have hh := norm_add_le w (z-w)
    rw [add_sub_cancel] at hh
    exact hh
  calc
    _ = |‖z‖-‖w‖| * (‖z‖+‖w‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),← abs_mul]
      congr 1
      ring
    _ ≤ ‖z-w‖*(‖z‖+‖w‖) :=
      mul_le_mul_of_nonneg_right hdiff (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := by nlinarith [norm_nonneg (z-w)]

lemma finite_signed_moment_error {ι : Type*} [Fintype ι] (f g : ι → ℂ) (s : ι → ℝ)
    (hs : ∀ i, |s i|≤1) (a ε : ℝ) (ha : 0≤a) (hε : 0≤ε)
    (herr : a*(∑ i, ‖f i-g i‖^2)≤ε^2) :
    |a*(∑ i, s i*‖f i‖^2)-a*(∑ i, s i*‖g i‖^2)| ≤
      2*Real.sqrt (a*∑ i, ‖g i‖^2)*ε+ε^2 := by
  have hS : 0≤∑ i, ‖g i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0≤∑ i, ‖f i-g i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖g i‖) (fun i => ‖f i-g i‖)
  have hse : Real.sqrt (a*∑ i, ‖f i-g i‖^2)≤ε :=
    (Real.sqrt_le_iff).mpr ⟨hε,herr⟩
  have hroot : a*(Real.sqrt (∑ i, ‖g i‖^2)*Real.sqrt (∑ i, ‖f i-g i‖^2))=
      Real.sqrt (a*∑ i, ‖g i‖^2)*Real.sqrt (a*∑ i, ‖f i-g i‖^2) := by
    rw [Real.sqrt_mul ha,Real.sqrt_mul ha]
    have hh := Real.sq_sqrt ha
    calc
      _ = (Real.sqrt a)^2*(Real.sqrt (∑ i, ‖g i‖^2)*Real.sqrt (∑ i, ‖f i-g i‖^2)) := by rw [hh]
      _ = _ := by ring
  have hc' : a*(∑ i, ‖g i‖*‖f i-g i‖)≤Real.sqrt (a*∑ i, ‖g i‖^2)*ε := by
    apply (mul_le_mul_of_nonneg_left hc ha).trans
    rw [hroot]
    exact mul_le_mul_of_nonneg_left hse (Real.sqrt_nonneg _)
  calc
    _ = a*|∑ i, s i*(‖f i‖^2-‖g i‖^2)| := by
      rw [← mul_sub,← Finset.sum_sub_distrib]
      simp only [← mul_sub,abs_mul,abs_of_nonneg ha]
    _ ≤ a*∑ i, |s i*(‖f i‖^2-‖g i‖^2)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) ha
    _ ≤ a*∑ i, (2*‖g i‖*‖f i-g i‖+‖f i-g i‖^2) := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hs i)).trans (norm_square_difference_le _ _)
    _ = 2*(a*∑ i, ‖g i‖*‖f i-g i‖)+a*∑ i, ‖f i-g i‖^2 := by
      simp only [Finset.sum_add_distrib, mul_assoc,← Finset.mul_sum]
      ring
    _ ≤ _ := by linarith

lemma wideSignedMoment_error (Ihat : Character experimentN → ℂ) (ε : ℝ) (hε : 0≤ε)
    (herr : (5760:ℝ)⁻¹*∑ χ : Character experimentN, ‖countingIntegral χ-Ihat χ‖^2 ≤ ε^2) :
    |wideCorrelation-approxSignedMoment Ihat| ≤
      2*Real.sqrt (approxDiagonalMoment Ihat)*ε+ε^2 := by
  rw [counting_signed_energy]
  exact finite_signed_moment_error countingIntegral Ihat (fun χ => (χ (-1)).re)
    (fun χ => (Complex.abs_re_le_norm _).trans (χ.norm_le_one _))
    _ ε (by positivity) hε herr

end LiLiuGoldbach16
