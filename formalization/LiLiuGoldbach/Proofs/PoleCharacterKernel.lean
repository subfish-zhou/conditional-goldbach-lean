import LiLiuGoldbach.Proofs.PoleLogDerivative

/-! The exact leading quadratic singularity of the finite character kernel. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Set Complex Filter
namespace LiLiuGoldbach16

lemma tendsto_real_add_nhdsNE (ρ : ℂ) :
    Tendsto (fun x : ℝ => ρ+(x:ℂ)) (𝓝[>] 0) (𝓝[≠] ρ) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun x : ℝ => ρ+(x:ℂ)) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change ρ+(x:ℂ) ≠ ρ
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 from ne_of_gt hx)
    simpa using hx0

lemma logDerivative_real_residue {N : ℕ} [NeZero N] (χ : Character N) (hχ : χ ≠ 1) (γ : ℝ) :
    Tendsto (fun x : ℝ => (x:ℂ)*logDerivative χ (line x γ)) (𝓝[>] 0)
      (𝓝 (analyticOrderNatAt χ.LFunction (line (1/2) γ):ℂ)) := by
  let ρ : ℂ := line (1/2) γ
  have ha := (χ.differentiable_LFunction hχ).analyticAt ρ
  have hn := LFunction_analyticOrder_ne_top χ hχ ρ
  have horder : meromorphicOrderAt χ.LFunction ρ = (analyticOrderNatAt χ.LFunction ρ:ℤ) := by
    rw [ha.meromorphicOrderAt_eq,← Nat.cast_analyticOrderNatAt hn]
    simp
  have hh := (logDeriv_residue_tendsto ha.meromorphicAt _ horder).comp (tendsto_real_add_nhdsNE ρ)
  have he : ∀x : ℝ, ρ+(x:ℂ) = 1/2+line x γ := by
    intro x
    dsimp [ρ,line]
    push_cast
    ring
  convert hh using 1
  · funext x
    change (x:ℂ)*logDeriv χ.LFunction (1/2+line x γ) =
      (ρ+(x:ℂ)-ρ)*logDeriv χ.LFunction (ρ+(x:ℂ))
    rw [add_sub_cancel_left,he]

lemma characterKernel_double_pole {N : ℕ} [NeZero N] (γ : ℝ) :
    Tendsto (fun x : ℝ => (x:ℂ)^2*characterKernel N (line x γ) (conj (line x γ)))
      (𝓝[>] 0) (𝓝 (poleCoefficient N γ:ℂ)) := by
  have hterm : ∀χ ∈ oddCharacters N,
      Tendsto (fun x : ℝ => (x:ℂ)^2*(logDerivative χ (line x γ)*conj (logDerivative χ (line x γ))))
        (𝓝[>] 0) (𝓝 ((analyticOrderNatAt χ.LFunction (line (1/2) γ):ℂ)^2)) := by
    intro χ hχ
    have hh := logDerivative_real_residue χ (odd_character_ne_one χ (Finset.mem_filter.mp hχ).2) γ
    have hc := hh.mul (Complex.continuous_conj.tendsto _ |>.comp hh)
    convert hc using 1
    · funext x
      change (x:ℂ)^2*(logDerivative χ (line x γ)*conj (logDerivative χ (line x γ))) =
        ((x:ℂ)*logDerivative χ (line x γ))*conj ((x:ℂ)*logDerivative χ (line x γ))
      rw [map_mul,Complex.conj_ofReal]
      ring
    · simp
      ring
  have hsum := (tendsto_finset_sum (oddCharacters N) hterm).const_mul ((2:ℂ)/(N.totient:ℂ))
  convert hsum using 1
  · funext x
    unfold characterKernel
    simp only [Complex.conj_conj]
    rw [← Finset.mul_sum]
    ring
  · unfold poleCoefficient
    push_cast
    rfl

end LiLiuGoldbach16
