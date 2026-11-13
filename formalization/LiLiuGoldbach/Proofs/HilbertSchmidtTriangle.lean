import LiLiuGoldbach.Proofs.SpectralTraceBounds

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LiLiuGoldbach16
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma hilbertSchmidt_sub_bound {T S : H →L[ℂ] H}
    (hT : IsHilbertSchmidt T) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (T-S) ∧ hsNorm (T-S)≤2*(hsNorm T+hsNorm S) := by
  obtain ⟨b,hb⟩ := hT
  have hT : IsHilbertSchmidt T := ⟨b,hb⟩
  obtain ⟨hST,hTS⟩ := proposition_5_3_hs_basis_independent T hT b
  obtain ⟨hSS,hSSq⟩ := proposition_5_3_hs_basis_independent S hS b
  have hpoint (j : ℕ) : ‖(T-S) (b j)‖^2≤2*(‖T (b j)‖^2+‖S (b j)‖^2) := by
    change ‖T (b j)-S (b j)‖^2≤_
    have h := norm_sub_le (T (b j)) (S (b j))
    nlinarith [norm_nonneg (T (b j)-S (b j)),norm_nonneg (T (b j)),norm_nonneg (S (b j)),sq_nonneg (‖T (b j)‖-‖S (b j)‖)]
  have hsum : Summable (fun j => ‖(T-S) (b j)‖^2) :=
    ((hST.add hSS).mul_left 2).of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
  have hsub : IsHilbertSchmidt (T-S) := ⟨b,hsum⟩
  refine ⟨hsub,?_⟩
  have he := (proposition_5_3_hs_basis_independent (T-S) hsub b).2
  have hsq : hsNorm (T-S)^2≤2*(hsNorm T^2+hsNorm S^2) := by
    rw [he,hTS,hSSq]
    convert Summable.tsum_le_tsum hpoint hsum ((hST.add hSS).mul_left 2) using 1
    rw [tsum_mul_left,hST.tsum_add hSS]
  have ht := hsNorm_nonneg T
  have hs := hsNorm_nonneg S
  have hts := hsNorm_nonneg (T-S)
  nlinarith [mul_nonneg ht hs]

lemma hilbertSchmidt_sub_sub_bound {P D K : H →L[ℂ] H}
    (hP : IsHilbertSchmidt P) (hD : IsHilbertSchmidt D) (hK : IsHilbertSchmidt K) :
    IsHilbertSchmidt (P-D-K) ∧ hsNorm (P-D-K)≤4*(hsNorm P+hsNorm D+hsNorm K) := by
  obtain ⟨hPD,hPDnorm⟩ := hilbertSchmidt_sub_bound hP hD
  obtain ⟨hR,hRnorm⟩ := hilbertSchmidt_sub_bound hPD hK
  exact ⟨hR,by linarith [hsNorm_nonneg K]⟩

end LiLiuGoldbach16
