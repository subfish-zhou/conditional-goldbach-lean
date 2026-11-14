module

public import ConditionalGoldbach.Proofs.SpectralPositiveFredholm
public import ConditionalGoldbach.Proofs.SpectralHilbertSchmidtCompact

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The paper's Hilbert--Schmidt norm is nonnegative, including its totalized zero case. -/
theorem hsNorm_nonneg (T : H →L[ℂ] H) : 0 ≤ hsNorm T := by
  unfold hsNorm
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

/-- The operator norm is at most the paper's original Hilbert--Schmidt norm. -/
theorem IsHilbertSchmidt.norm_le_hsNorm {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    ‖T‖ ≤ hsNorm T := by
  unfold IsHilbertSchmidt at hT
  unfold hsNorm
  rw [dite_eq_left hT]
  exact hilbertSchmidt_norm_le T (Classical.choose hT) (Classical.choose_spec hT)

/-- For a positive trace-class operator, its Hilbert--Schmidt norm is at most its trace. -/
theorem IsPositiveTraceClass.hsNorm_le_trace {A : H →L[ℂ] H} (hA : IsPositiveTraceClass A) :
    hsNorm A ≤ positiveTrace A := by
  obtain ⟨-, -, hspec, hpos, hsum, htrace, -, -⟩ := proposition_6_1_positive_fredholm_spec A hA
  have hsq : hsNorm A ^ 2 = ∑' j, eigenvalues A j ^ 2 := by
    simpa only [eigenvalues, dite_eq_left hspec] using (Classical.choice hspec).hsNorm_sq
  have hnonneg : 0 ≤ positiveTrace A := htrace ▸ tsum_nonneg hpos
  have hle : (∑' j, eigenvalues A j ^ 2) ≤ (positiveTrace A) ^ 2 := by
    calc
      (∑' j, eigenvalues A j ^ 2) ≤ ∑' j, eigenvalues A j * positiveTrace A := by
        apply Summable.tsum_le_tsum ?_ (eigenvalues_square_summable A hspec)
          (hsum.mul_right (positiveTrace A))
        intro j
        have hj : eigenvalues A j ≤ positiveTrace A := by
          rw [htrace]
          exact hsum.le_tsum j (fun i hi => hpos i)
        nlinarith [hpos j]
      _ = (positiveTrace A) ^ 2 := by rw [tsum_mul_right, ← htrace, pow_two]
  rw [← hsq] at hle
  nlinarith [hsNorm_nonneg A]

end ConditionalGoldbach
