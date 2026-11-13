import ConditionalGoldbach.Definitions

/-! Derivative convergence from pointwise convergence and a common circular majorant. -/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Set Complex Metric Filter MeasureTheory
namespace ConditionalGoldbach

lemma deriv_tendsto_of_bounded_circle (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (c : ℂ) (r B : ℝ) (hr : 0 < r)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (closedBall c r))
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hb : ∀ᶠ n in atTop, ∀z ∈ sphere c r, ‖F n z‖ ≤ B)
    (hlim : ∀z ∈ sphere c r, Tendsto (fun n => F n z) atTop (𝓝 (f z))) :
    Tendsto (fun n => deriv (F n) c) atTop (𝓝 (deriv f c)) := by
  let K : ℝ → ℂ := fun θ => deriv (circleMap c r) θ * (1/(circleMap c r θ-c)^2)
  have hne : ∀θ, circleMap c r θ-c ≠ 0 := by
    intro θ
    rw [circleMap_sub_center]
    exact norm_ne_zero_iff.mp (by simpa [norm_circleMap_zero,abs_of_pos hr] using hr.ne')
  have hK : Continuous K := by
    dsimp [K]
    simp_rw [deriv_circleMap]
    exact (by fun_prop : Continuous (fun θ => circleMap 0 r θ * I)).mul
      (continuous_const.div ((continuous_circleMap _ _).sub continuous_const |>.pow 2)
        (fun θ => pow_ne_zero _ (hne θ)))
  have hKb : ∀θ, ‖K θ‖ = r*(1/r^2) := by
    intro θ
    simp [K,deriv_circleMap,norm_mul,norm_div,norm_pow,circleMap_sub_center,
      norm_circleMap_zero,abs_of_pos hr]
  have hcF : ∀ᶠ n in atTop, Continuous (fun θ => K θ * F n (circleMap c r θ)) := by
    filter_upwards [hF] with n hn
    apply hK.mul
    exact hn.continuousOn.comp_continuous (continuous_circleMap _ _)
      (fun θ => sphere_subset_closedBall (circleMap_mem_sphere _ hr.le _))
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc 0 (2*Real.pi))) (fun _ : ℝ => r*(1/r^2)*B)
    (hcF.mono fun n hn => hn.aestronglyMeasurable)
    (hb.mono fun n hn => ae_of_all _ fun θ => by
      rw [norm_mul,hKb]
      exact mul_le_mul_of_nonneg_left (hn _ (circleMap_mem_sphere _ hr.le _)) (by positivity))
    (integrable_const _) (ae_of_all _ fun θ =>
      (hlim _ (circleMap_mem_sphere _ hr.le _)).const_mul (K θ))
  have hi' : Tendsto (fun n => ∮ z in C(c,r), (1/(z-c)^2) • F n z) atTop
      (𝓝 (∮ z in C(c,r), (1/(z-c)^2) • f z)) := by
    simpa only [circleIntegral_def_Icc,smul_eq_mul,mul_assoc,K] using hi
  have he : ∀ᶠ n in atTop, (∮ z in C(c,r), (1/(z-c)^2) • F n z) =
      (2*Real.pi*I) * deriv (F n) c :=
    hF.mono fun n hn => hn.deriv_eq_smul_circleIntegral hr
  rw [hf.deriv_eq_smul_circleIntegral hr,smul_eq_mul] at hi'
  have hlim' := (hi'.congr' he).const_mul ((2*Real.pi*I : ℂ)⁻¹)
  simpa [← mul_assoc, two_pi_I_ne_zero] using hlim'

end ConditionalGoldbach
