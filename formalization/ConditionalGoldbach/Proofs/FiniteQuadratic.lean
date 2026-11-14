module

public import ConditionalGoldbach.Proofs.FiniteFunctional
public import ConditionalGoldbach.Proofs.QuadraticIdentity

/-! Recovery of a kernel quadratic form from any represented finite-smooth Mellin functional. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma real_mellin_conj (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun u => (f u : ℂ)) (conj s) = conj (mellin (fun u => (f u : ℂ)) s) := by
  unfold mellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [smul_eq_mul,map_mul,conj_ofReal]
  rw [← ofReal_cpow_conj u hu,map_sub,map_one]

lemma finite_mellin_coefficient_conj (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) (s : ℂ) :
    (N : ℂ)^conj s * mellin (fun u => (f u : ℂ)) (conj s) * (1+conj s) =
      conj ((N : ℂ)^s*mellin (fun u => (f u : ℂ)) s*(1+s)) := by
  rw [← ofReal_natCast,ofReal_cpow_conj (N : ℝ) (by exact_mod_cast hN),real_mellin_conj]
  simp only [map_mul,map_add,map_one]

lemma finite_functional_kernel_recovery {a : ℝ} (N : ℕ) (hN : 0 < N)
    (f : ℝ → ℝ) (σ : ℝ) (hσ : σ ∈ Ioo a beta)
    (v : HardySpace a beta)
    (hv : ∀ ψ, finiteFunctionalValue N f σ ψ = paperInner ψ v)
    (T : HardySpace a beta →L[ℂ] HardySpace a beta) (K : ℂ → ℂ → ℂ)
    (hK : ∀ s z : ℂ, s ∈ strip a beta → z ∈ strip a beta →
      K s z = paperInner (T (evaluationVector z)) (evaluationVector s))
    (s : ℂ) (hs : s ∈ strip a beta) :
    fourierLaplace (T v) s = verticalMellin σ (fun z =>
      (N : ℂ)^z*mellin (fun u => (f u : ℂ)) z*(1+z)*K s (conj z)) := by
  have hstart : fourierLaplace (T v) s =
      conj (finiteFunctionalValue N f σ (T.adjoint (evaluationVector s))) := by
    rw [hv,evaluationVector_spec hs]
    unfold paperInner
    rw [inner_conj_symm]
    exact (T.adjoint_inner_left v (evaluationVector s)).symm
  rw [hstart,finiteFunctionalValue,verticalMellin_conj]
  unfold verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let z := line σ t
  have hz : conj z ∈ strip a beta := by simpa [z,strip,line] using hσ
  change conj ((N : ℂ)^conj z*mellin (fun u => (f u : ℂ)) (conj z)*(1+conj z)*
    fourierLaplace (T.adjoint (evaluationVector s)) (conj z)) = _
  rw [map_mul,finite_mellin_coefficient_conj N hN f z,conj_conj,
    evaluationVector_spec hz,hK s (conj z) hs hz]
  congr 1
  unfold paperInner
  rw [inner_conj_symm]
  exact T.adjoint_inner_left (evaluationVector (conj z)) (evaluationVector s)

lemma finite_quadratic_residual_integral {a : ℝ} (N : ℕ) [NeZero N]
    (f : ℝ → ℝ) (σ : ℝ) (hσ : σ ∈ Ioo a beta) (hσ0 : 0 < σ)
    (v : HardySpace a beta)
    (hv : ∀ ψ, finiteFunctionalValue N f σ ψ = paperInner ψ v)
    (T : HardySpace a beta →L[ℂ] HardySpace a beta)
    (hK : ∀ s z : ℂ, s ∈ strip a beta → z ∈ strip a beta →
      weightedKernel N s z = paperInner (T (evaluationVector z)) (evaluationVector s)) :
    paperInner (T v) v = verticalMellin σ (fun s => verticalMellin σ (fun z =>
      (N : ℂ)^(s+z)*mellin (fun u => (f u : ℂ)) s*mellin (fun u => (f u : ℂ)) z*
        residual N s z)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← hv (T v)]
  unfold finiteFunctionalValue verticalMellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  let s := line σ t
  have hs : s ∈ strip a beta := by simpa [s,strip,line] using hσ
  change (N : ℂ)^s*mellin (fun u => (f u : ℂ)) s*(1+s)*fourierLaplace (T v) s = _
  rw [finite_functional_kernel_recovery N hN f σ hσ v hv T (weightedKernel N) hK s hs]
  unfold verticalMellin
  rw [mul_left_comm _ ((2*(Real.pi : ℂ))⁻¹),← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  let z := line σ y
  have hs0 : 1+s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s,line] at hr
    linarith
  have hz0 : 1+z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [z,line] at hr
    linarith
  change (N : ℂ)^s*mellin (fun u => (f u : ℂ)) s*(1+s)*
    ((N : ℂ)^z*mellin (fun u => (f u : ℂ)) z*(1+z)*weightedKernel N s (conj z)) = _
  simp only [weightedKernel,conj_conj]
  rw [cpow_add _ _ hNz]
  field_simp; ring

end ConditionalGoldbach
