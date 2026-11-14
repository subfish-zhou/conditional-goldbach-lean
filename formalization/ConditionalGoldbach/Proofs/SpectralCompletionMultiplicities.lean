module

public import ConditionalGoldbach.Proofs.SpectralCompletionDeterminant
import Mathlib.Analysis.Calculus.Deriv.Star

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem spectralComplex_one_sub (N : ℕ) (T : H →L[ℂ] H) (q : ℂ) :
    spectralComplex N T (1 - q) = spectralComplex N T q := by
  apply tprod_congr
  intro j
  ring

theorem iteratedDeriv_conjugate (n : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv n f ∘ conj := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, iteratedDeriv_succ]

theorem analyticOrderNatAt_reflection (f : ℂ → ℂ) (hf : ∀ z, f (1 - z) = f z) (z : ℂ) :
    analyticOrderNatAt f z = analyticOrderNatAt f (1 - z) := by
  have hfun : f ∘ (fun z => 1 - z) = f := funext hf
  have hh := analyticOrderAt_comp_of_deriv_ne_zero (f := f) (z₀ := z)
    (g := fun z : ℂ => 1 - z) (by fun_prop) (by simp)
  simp only [hfun] at hh
  exact congrArg ENat.toNat hh

theorem analyticOrderNatAt_conjugate (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    analyticOrderNatAt f z = analyticOrderNatAt f (conj z) := by
  have hfun : conj ∘ f ∘ conj = f := by
    funext w
    simp only [Function.comp_apply, hconj, conj_conj]
  have hderiv (k : ℕ) : iteratedDeriv k f (conj z) = conj (iteratedDeriv k f z) := by
    have hh := congrFun (iteratedDeriv_conjugate k f) (conj z)
    simpa only [hfun, Function.comp_apply, conj_conj] using hh
  have ho : analyticOrderAt f z = analyticOrderAt f (conj z) := by
    apply ENat.eq_of_forall_natCast_le_iff
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.analyticAt z),
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.analyticAt (conj z))]
    simp only [hderiv, map_eq_zero]
  exact congrArg ENat.toNat ho

/-- Reflection around one half forces even central vanishing order. -/
theorem analyticOrderNatAt_center_even (f : ℂ → ℂ) (hf : AnalyticAt ℂ f (1 / 2))
    (hreflect : ∀ z, f (1 - z) = f z) : Even (analyticOrderNatAt f (1 / 2)) := by
  by_cases htop : analyticOrderAt f (1 / 2) = ⊤
  · simp only [analyticOrderNatAt, htop, ENat.toNat_top]
    exact ⟨0, rfl⟩
  let n := analyticOrderNatAt f (1 / 2)
  have horder : analyticOrderAt f (1 / 2) = (n : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt htop).symm
  have hn := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).1 horder |>.2
  have hfun : (fun z : ℂ => f (1 - z)) = f := funext hreflect
  have hh := congrFun (iteratedDeriv_comp_const_sub n f 1) (1 / 2 : ℂ)
  simp only [hfun, sub_half, smul_eq_mul] at hh
  by_contra heven
  have hodd : Odd n := Nat.not_even_iff_odd.mp heven
  rw [hodd.neg_one_pow] at hh
  apply hn
  linear_combination (1 / 2 : ℂ) * hh

theorem quaternion_quadratic_conjugation (q u : Quaternion ℝ) (hu : ‖u‖ = 1)
    (c : ℝ) (hroot : q * (1 - q) = (c : Quaternion ℝ)) :
    (u * q * star u) * (1 - u * q * star u) = (c : Quaternion ℝ) := by
  have hnorm : Quaternion.normSq u = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hu]; norm_num
  have hright : u * star u = 1 := by rw [Quaternion.self_mul_star, hnorm, Quaternion.coe_one]
  have hleft : star u * u = 1 := by rw [Quaternion.star_mul_self, hnorm, Quaternion.coe_one]
  have hsub : 1 - u * q * star u = u * (1 - q) * star u := by
    simp only [mul_sub, mul_one, sub_mul, hright]
  rw [hsub]
  calc
    (u * q * star u) * (u * (1 - q) * star u) =
        u * (q * (star u * u) * (1 - q)) * star u := by noncomm_ring
    _ = u * (q * (1 - q)) * star u := by rw [hleft, mul_one]
    _ = u * (c : Quaternion ℝ) * star u := by rw [hroot]
    _ = (c : Quaternion ℝ) := by
      rw [Quaternion.mul_coe_eq_smul, Algebra.smul_mul_assoc, hright,
        ← Quaternion.coe_one, Quaternion.smul_coe, mul_one]

theorem proposition_6_3_multiplicities (N : ℕ) [NeZero N]
    (hN : Even N) (hlarge : Real.exp 10 < (N : ℝ))
    (hGRH : GRH N) (ha : alpha N < beta) :
    (∀ q : ℂ, analyticOrderNatAt (spectralComplex N (residualOperator ha N)) q =
      analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (1 - q)) ∧
    (∀ q : ℂ, analyticOrderNatAt (spectralComplex N (residualOperator ha N)) q =
      analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (conj q)) ∧
    Even (analyticOrderNatAt (spectralComplex N (residualOperator ha N)) (1 / 2)) ∧
    (∀ q u : Quaternion ℝ, ‖u‖ = 1 →
      spectralQuaternion N (residualOperator ha N) q = 0 →
      spectralQuaternion N (residualOperator ha N) (u * q * star u) = 0) := by
  have hT := residualOperator_has_spectral_data N hN hlarge hGRH ha
  have hf := spectralComplex_differentiable N _ hT
  refine ⟨analyticOrderNatAt_reflection _ (spectralComplex_one_sub N _),
    analyticOrderNatAt_conjugate _ hf (spectralComplex_conj N _ hT),
    analyticOrderNatAt_center_even _ (hf.analyticAt _) (spectralComplex_one_sub N _), ?_⟩
  intro q u hu hzero
  have hparam := large_parameters hlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hδ := spectralScale_pos N hNpos (singularSeries_pos N) hparam.2.1
  obtain ⟨j, hμ, hroot⟩ := (spectralQuaternion_eq_zero_iff N _ hT hδ.ne' q).1 hzero
  exact (spectralQuaternion_eq_zero_iff N _ hT hδ.ne' _).2
    ⟨j, hμ, quaternion_quadratic_conjugation q u hu _ hroot⟩

end ConditionalGoldbach
