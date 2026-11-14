module

public import ConditionalGoldbach.Proofs.GammaSequenceBounds
public import ConditionalGoldbach.Proofs.CauchyBoundedLimit

/-! Euler's Gamma products converge also at the level of logarithmic derivatives. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Set Complex Metric Filter
namespace ConditionalGoldbach

lemma GammaSeq_deriv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n => deriv (fun z => Complex.GammaSeq z n) s) atTop (𝓝 (deriv Gamma s)) := by
  let r : ℝ := s.re/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : ∀z ∈ closedBall s r, z.re ∈ Icc r (3*s.re/2) := by
    intro z hz
    have hh := abs_re_le_norm (z-s)
    have hh' := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm] at hh'
    simp only [sub_re,abs_le] at hh
    dsimp [r] at *
    constructor <;> linarith
  apply deriv_tendsto_of_bounded_circle (fun n z => Complex.GammaSeq z n) Gamma s r
    (max (Real.Gamma r) (Real.Gamma (3*s.re/2))) hr
  · filter_upwards [eventually_ne_atTop 0] with n hn
    intro z hz
    exact (GammaSeq_differentiableAt (lt_of_lt_of_le hr (hre z hz).1) hn).differentiableWithinAt
  · intro z hz
    exact (hasDerivAt_Gamma_of_re_pos (lt_of_lt_of_le hr (hre z hz).1)).differentiableAt.differentiableWithinAt
  · filter_upwards [eventually_ne_atTop 0] with n hn z hz
    have hz' := hre z (sphere_subset_closedBall hz)
    apply (GammaSeq_norm_le_Gamma_re (lt_of_lt_of_le hr hz'.1) hn).trans
    exact Real.convexOn_Gamma.le_max_of_mem_Icc hr (by change 0 < 3*s.re/2; positivity) hz'
  · intro z hz
    exact GammaSeq_tendsto_Gamma z

lemma GammaSeq_logDeriv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n => logDeriv (fun z => Complex.GammaSeq z n) s) atTop
      (𝓝 (logDeriv Gamma s)) :=
  (GammaSeq_deriv_tendsto hs).div (GammaSeq_tendsto_Gamma s) (Gamma_ne_zero_of_re_pos hs)

lemma GammaSeq_logDeriv {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun z => Complex.GammaSeq z n) s =
      Complex.log (n:ℂ) - ∑ j ∈ Finset.range (n+1), 1/(s+(j:ℂ)) := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have hpn : ∀j : ℕ, s+(j:ℂ) ≠ 0 := by
    intro j he
    have hh := congrArg Complex.re he
    simp only [add_re,natCast_re,zero_re] at hh
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  let P : ℂ → ℂ := fun z => ∏ j ∈ Finset.range (n+1), (z+(j:ℂ))
  have hP : DifferentiableAt ℂ P s :=
    DifferentiableAt.fun_finsetProd (fun j _ => differentiableAt_id.add_const _)
  have hPn : P s ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hpn j)
  have hQ := (differentiableAt_id.const_cpow (Or.inl hnC) : DifferentiableAt ℂ (fun z : ℂ => (n:ℂ)^z) s)
  have hQn : (n:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hfact : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  change logDeriv (fun z => ((n:ℂ)^z*(n.factorial:ℂ))/P z) s = _
  rw [logDeriv_fun_div (f := fun z : ℂ => (n:ℂ)^z*(n.factorial:ℂ)) (g := P) s (mul_ne_zero hQn hfact) hPn (hQ.mul_const _) hP,
    logDeriv_fun_mul (f := fun z : ℂ => (n:ℂ)^z) (g := fun _ : ℂ => (n.factorial:ℂ)) s hQn hfact hQ (differentiableAt_const _)]
  have hcp : logDeriv (fun z : ℂ => (n:ℂ)^z) s = Complex.log (n:ℂ) := by
    simpa using logDeriv_cpow_affine (n:ℂ) 1 0 s hnC
  rw [hcp,logDeriv_const]
  simp only [Pi.zero_apply,add_zero]
  congr 1
  have hPe : P = ∏ j ∈ Finset.range (n+1), fun z : ℂ => z+(j:ℂ) := by
    funext z
    simp [P]
  rw [hPe]
  rw [logDeriv_prod (fun j _ => hpn j) (fun j _ => differentiableAt_id.add_const _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [logDeriv_apply,((hasDerivAt_id' s).add_const (j:ℂ)).deriv]

end ConditionalGoldbach
