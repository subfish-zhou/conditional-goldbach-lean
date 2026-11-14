module

public import ConditionalGoldbach.Proofs.SpectralCompletionChoice
public import ConditionalGoldbach.Proofs.SpectralCompletionIdentities

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual Fredholm product of the squared operator, not a chosen-eigenbasis surrogate. -/
theorem spectralSquare_determinant_spec (T : H →L[ℂ] H) (hT : Nonempty (SpectralData T)) :
    Nonempty (SpectralData (T.comp T)) ∧
    positiveTrace (T.comp T) = ∑' j, eigenvalues T j ^ 2 ∧
    (∀ t : ℂ, Multipliable (fun j : ℕ => 1 - t * (eigenvalues T j : ℂ) ^ 2) ∧
      fredholmSquareDet T t = ∏' j : ℕ, (1 - t * (eigenvalues T j : ℂ) ^ 2)) := by
  let d := Classical.choice hT
  have hA : Nonempty (SpectralData (T.comp T)) := ⟨d.square⟩
  let dA := Classical.choice hA
  have heig : eigenvalues T = d.values := by simp only [eigenvalues, dite_eq_left hT, d]
  refine ⟨hA, ?_, ?_⟩
  · rw [symmetric_square_trace_eq_hsNorm T d.isSymmetric d.isHilbertSchmidt, d.hsNorm_sq, heig]
  · intro t
    have hs : Summable (fun j => -(t * (d.values j : ℂ) ^ 2)) := by
      simpa only [Complex.ofReal_pow] using
        ((Complex.summable_ofReal.2 d.squareSummable).mul_left t).neg
    refine ⟨?_, ?_⟩
    · simpa only [heig, sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs
    · have hsSquare : Summable (fun j => -(t * (d.square.values j : ℂ))) := by
        simpa only [SpectralData.square, Complex.ofReal_pow] using hs
      have hsA := (d.square.spectralStatistic_independent dA (fun x => -(t * (x : ℂ))) hsSquare).1
      have hp := dA.tprod_one_add_independent d.square (fun x => -(t * (x : ℂ))) hsA hsSquare
      simpa only [fredholmSquareDet, positiveFredholmDet, eigenvalues, dite_eq_left hA,
        dite_eq_left hT, d, dA, SpectralData.square, Complex.ofReal_pow, sub_eq_add_neg] using hp

theorem proposition_6_1_square_determinant (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta) :
    let T := residualOperator ha N
    Nonempty (SpectralData (T.comp T)) ∧
    positiveTrace (T.comp T) = ∑' j, eigenvalues T j ^ 2 ∧
    (∀ t : ℂ, Multipliable (fun j : ℕ => 1 - t * (eigenvalues T j : ℂ) ^ 2) ∧
      fredholmSquareDet T t = ∏' j : ℕ, (1 - t * (eigenvalues T j : ℂ) ^ 2)) := by
  exact spectralSquare_determinant_spec _ (residualOperator_has_spectral_data N hN hlarge hGRH ha)

theorem proposition_6_1 (N : ℕ) [NeZero N] (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    CompactUniformLimit (fun k q => spectralPartialQuaternion N (residualOperator ha N) q k)
      (spectralQuaternion N (residualOperator ha N)) ∧
    IntrinsicEntire (spectralQuaternion N (residualOperator ha N)) ∧
    (∀ q : ℂ, Multipliable (fun j : ℕ =>
      1 - (4 * eigenvalues (residualOperator ha N) j ^ 2 / spectralScale N ^ 2 : ℝ) *
        q * (1 - q))) ∧
    IsPositiveTraceClass ((residualOperator ha N).comp (residualOperator ha N)) ∧
    positiveTrace ((residualOperator ha N).comp (residualOperator ha N)) =
      hsNorm (residualOperator ha N) ^ 2 ∧
    (∀ q : ℂ, spectralComplex N (residualOperator ha N) q =
      fredholmSquareDet (residualOperator ha N) (4 / spectralScale N ^ 2 * q * (1 - q))) := by
  have hT := residualOperator_has_spectral_data N hN hlarge hGRH ha
  let d := Classical.choice hT
  refine ⟨spectralQuaternion_compactUniformLimit N _ hT,
    spectralQuaternion_intrinsicEntire N _ hT, spectralComplex_multipliable N _ hT,
    symmetric_square_positiveTraceClass _ d.isSymmetric d.isHilbertSchmidt,
    symmetric_square_trace_eq_hsNorm _ d.isSymmetric d.isHilbertSchmidt, ?_⟩
  intro q
  rw [((spectralSquare_determinant_spec _ hT).2.2 _).2]
  apply tprod_congr
  intro j
  push_cast
  ring

end ConditionalGoldbach
