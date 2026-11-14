module

public import ConditionalGoldbach.Proofs.LogDerivativeDisk
public import ConditionalGoldbach.Proofs.CharacterGrowthFoundation

/-! The GRH logarithmic-derivative bound obtained from zero-free disks, independently of Hadamard products. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex Metric
namespace ConditionalGoldbach

lemma logDerivative_uniform_bound (δ M : ℝ) (hδ : 0 < δ) (hM : δ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ (_ : NeZero N), 4 ≤ N → GRH N →
      ∀ χ : Character N, χ ≠ 1 → ∀ σ ∈ Icc δ M, ∀ t : ℝ,
        ‖logDerivative χ (line σ t)‖ ≤ C * Real.log (N*(|t|+2))^2 := by
  let R : ℝ := M+5/2-δ/2
  let r : ℝ := M+5/2-δ
  let A : ℝ := 4*M+13
  let K : ℝ := 8*R/(R-r)^2
  have hMpos : 0 < M := hδ.trans_le hM
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r,R]; linarith
  have hR : 0 < R := hr.trans_lt hrR
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K*(2*A+1), by positivity, fun N _ hN hGRH χ hχ σ hσ t => ?_⟩
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  let X : ℝ := (N : ℝ)*(|t|+2)
  have hX : 8 ≤ X := by
    dsimp only [X]
    nlinarith only [hNr, mul_nonneg hNpos.le (abs_nonneg t)]
  have hXpos : 0 < X := by linarith
  let c : ℂ := ((M+3 : ℝ) : ℂ)+(t : ℂ)*I
  let f : ℂ → ℂ := fun u => χ.LFunction (c+u)
  let z : ℂ := 1/2+line σ t-c
  have hcre : c.re = M+3 := by simp [c]
  have hcnorm : ‖c‖ ≤ M+3+|t| := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
    rw [abs_of_pos (by linarith : 0 < M+3)]
  have hF : AnalyticOnNhd ℂ f (ball 0 R) := by
    intro u _
    exact ((χ.differentiable_LFunction hχ).analyticAt _).comp
      (analyticAt_const.add analyticAt_id)
  have hright (u : ℂ) (hu : u ∈ ball (0 : ℂ) R) : 1/2 < (c+u).re := by
    have hn := mem_ball_zero_iff.mp hu
    have hre : -‖u‖ ≤ u.re := by
      have hh := (neg_le_abs u.re).trans (Complex.abs_re_le_norm u)
      linarith
    rw [add_re,hcre]
    dsimp [R] at hn
    linarith
  have hnon (u : ℂ) (hu : u ∈ ball (0 : ℂ) R) : f u ≠ 0 :=
    LFunction_ne_zero_of_GRH hGRH χ hχ (hright u hu)
  have hflower : (1/2 : ℝ) ≤ ‖f 0‖ := by
    simpa only [f,add_zero] using LFunction_right_lower_bound χ c (by rw [hcre]; linarith)
  have hupper (u : ℂ) (hu : u ∈ ball (0 : ℂ) R) : ‖f u‖ ≤ A*X := by
    have hp := hright u hu
    have hpoly := LFunction_polynomial_bound χ hχ (c+u) (by linarith)
    have hinv : ‖c+u‖/(c+u).re ≤ 2*‖c+u‖ := by
      have h := div_le_div_of_nonneg_left (norm_nonneg (c+u)) (by norm_num : (0 : ℝ) < 1/2) hp.le
      convert h using 1; ring
    have hnorm := norm_add_le c u
    have hunorm := mem_ball_zero_iff.mp hu
    have hscl : 1+2*‖c+u‖ ≤ A*(|t|+2) := by
      dsimp only [A]
      dsimp only [R] at hunorm
      nlinarith only [hnorm, hcnorm, hunorm, hδ, hMpos, abs_nonneg t,
        mul_nonneg hMpos.le (abs_nonneg t)]
    calc
      ‖f u‖ ≤ (N : ℝ)*(1+‖c+u‖/(c+u).re) := hpoly
      _ ≤ (N : ℝ)*(A*(|t|+2)) := mul_le_mul_of_nonneg_left (by linarith) hNpos.le
      _ = A*X := by dsimp [X]; ring
  have hz : ‖z‖ ≤ r := by
    have he : z = ((σ-M-5/2 : ℝ) : ℂ) := by dsimp [z,c,line]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hσ.2])]
    dsimp [r]
    linarith [hσ.1]
  have hU : (1/2 : ℝ) < A*X := by
    dsimp only [A]
    nlinarith only [hX, mul_nonneg hMpos.le hXpos.le]
  have hb := logDerivative_disk_bound f R r (A*X) (1/2) hR hr hrR (by norm_num) hU
    hF hnon hflower hupper z hz
  have hdf : deriv f z = deriv χ.LFunction (1/2+line σ t) := by
    have hh := ((χ.differentiable_LFunction hχ (c+z)).hasDerivAt).comp z
      ((hasDerivAt_id z).const_add c)
    have he : c+z = 1/2+line σ t := by dsimp [z]; ring
    simpa only [f,Function.comp_def,he,mul_one] using hh.deriv
  have hfz : f z = χ.LFunction (1/2+line σ t) := by dsimp [f,z]; congr 1; ring
  rw [hdf,hfz] at hb
  change ‖logDerivative χ (line σ t)‖ ≤ K*Real.log (A*X/(1/2)) at hb
  have hlog : 1 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).mpr
    exact (Real.exp_one_lt_three.le).trans (by linarith)
  have hlogbound : Real.log (A*X/(1/2)) ≤ (2*A+1)*Real.log X^2 := by
    rw [show A*X/(1/2) = (2*A)*X by ring,
      Real.log_mul (by positivity : 2*A ≠ 0) hXpos.ne']
    have hlogA : Real.log (2*A) ≤ 2*A := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2*A)
      linarith
    have hlogA' : Real.log (2*A) ≤ (2*A)*Real.log X :=
      hlogA.trans (le_mul_of_one_le_right (by positivity) hlog)
    have hlogpow : Real.log X ≤ Real.log X^2 := by nlinarith only [hlog]
    calc
      _ ≤ (2*A+1)*Real.log X := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogpow (by positivity)
  exact hb.trans (by convert mul_le_mul_of_nonneg_left hlogbound hK.le using 1; dsimp [X]; ring)

end ConditionalGoldbach
