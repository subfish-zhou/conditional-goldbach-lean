import ConditionalGoldbach.Proofs.VariableComponentOperators
import ConditionalGoldbach.Proofs.CharacterStripTrace
import ConditionalGoldbach.Proofs.SpectralDiagonalBound
import ConditionalGoldbach.Proofs.HilbertSchmidtTriangle

set_option autoImplicit false
noncomputable section
namespace ConditionalGoldbach

lemma component_bounds_of_average (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), 4≤N → GRH N →
      (∀ σ : ℝ, 0<σ → σ≤beta → averagedLogDerivative N σ≤A*(Real.log N^2+σ⁻¹^2)) →
      ∀ a : ℝ, 0<a → ∀ ha : a<beta,
        IsPositiveTraceClass (arithmeticOperator ha N) ∧
        IsPositiveTraceClass (diagonalOperator ha N) ∧
        IsHilbertSchmidt (modelOperator ha N) ∧
        (hsNorm (arithmeticOperator ha N)≤positiveTrace (arithmeticOperator ha N) ∧
          positiveTrace (arithmeticOperator ha N)≤C*(Real.log N^2+a⁻¹^2)) ∧
        (hsNorm (diagonalOperator ha N)≤positiveTrace (diagonalOperator ha N) ∧
          positiveTrace (diagonalOperator ha N)≤C*a⁻¹^2) ∧
        hsNorm (modelOperator ha N)≤C*a⁻¹^2 := by
  obtain ⟨K,hK,hmodel⟩ := modelOperator_uniform_hs_bound
  let D := 2*Real.pi*(Real.log 4+4)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨2*A+D+K,by positivity,?_⟩
  intro N _ hN4 hGRH havg a ha0 ha
  obtain ⟨hp,hps,hpt⟩ := arithmeticOperator_trace_bound_of_average_on_strip N hN4 hGRH ha0 ha A hA.le havg
  obtain ⟨hd,hds,hdt⟩ := diagonalOperator_trace_bound ha ha0 N
  obtain ⟨hk,hks⟩ := hmodel a ha0 ha N inferInstance
  refine ⟨hp,hd,hk,⟨hps,?_⟩,⟨hds,?_⟩,?_⟩
  · exact hpt.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact hdt.trans (mul_le_mul_of_nonneg_right (by dsimp [D] at *; linarith) (by positivity))
  · exact hks.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

lemma residual_bound_of_components (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0<a) (hN4 : 4≤N) (hGRH : GRH N) (ha : a<beta) (C : ℝ) (hC : 0≤C)
    (hP : IsPositiveTraceClass (arithmeticOperator ha N))
    (hD : IsPositiveTraceClass (diagonalOperator ha N))
    (hK : IsHilbertSchmidt (modelOperator ha N))
    (hp : positiveTrace (arithmeticOperator ha N)≤C*(Real.log N^2+a⁻¹^2))
    (hd : positiveTrace (diagonalOperator ha N)≤C*a⁻¹^2)
    (hk : hsNorm (modelOperator ha N)≤C*a⁻¹^2) :
    IsHilbertSchmidt (residualOperator ha N) ∧
      ‖residualOperator ha N‖≤hsNorm (residualOperator ha N) ∧
      hsNorm (residualOperator ha N)≤12*C*(Real.log N^2+a⁻¹^2) := by
  rw [residualOperator_components_at a N ha0 hN4 hGRH ha]
  obtain ⟨hR,hr⟩ := hilbertSchmidt_sub_sub_bound hP.isHilbertSchmidt hD.isHilbertSchmidt hK
  refine ⟨hR,hR.norm_le_hsNorm,?_⟩
  have hp' := hP.hsNorm_le_trace.trans hp
  have hd' := hD.hsNorm_le_trace.trans hd
  nlinarith [mul_nonneg hC (sq_nonneg (Real.log N))]

lemma residual_bound_of_average (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), 4≤N → GRH N →
      (∀ σ : ℝ, 0<σ → σ≤beta → averagedLogDerivative N σ≤A*(Real.log N^2+σ⁻¹^2)) →
      ∀ a : ℝ, 0<a → ∀ ha : a<beta,
        IsHilbertSchmidt (residualOperator ha N) ∧
        ‖residualOperator ha N‖≤hsNorm (residualOperator ha N) ∧
        hsNorm (residualOperator ha N)≤C*(Real.log N^2+a⁻¹^2) := by
  obtain ⟨C,hC,hcomp⟩ := component_bounds_of_average A hA
  refine ⟨12*C,by positivity,?_⟩
  intro N _ hN4 hGRH havg a ha0 ha
  obtain ⟨hP,hD,hK,hp,hd,hk⟩ := hcomp N inferInstance hN4 hGRH havg a ha0 ha
  exact residual_bound_of_components a N ha0 hN4 hGRH ha C hC.le hP hD hK hp.2 hd.2 hk

end ConditionalGoldbach
