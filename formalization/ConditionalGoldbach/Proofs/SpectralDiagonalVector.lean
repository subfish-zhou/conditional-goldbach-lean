module

public import ConditionalGoldbach.Proofs.HardyContinuousBoundary
public import ConditionalGoldbach.Proofs.SpectralPoissonConvolution

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- Exact square modulus of the diagonal rank-one vector on a vertical line. -/
theorem diagonalVector_norm_sq (n : ℕ) (hn : 1 ≤ n) (x t : ℝ) :
    ‖diagonalVector n (line x t)‖ ^ 2 = (n : ℝ) ^ (-2 * x) / ((1 + x) ^ 2 + t ^ 2) := by
  unfold diagonalVector
  rw [norm_div, div_pow, Complex.norm_natCast_cpow_of_pos (by omega), Complex.sq_norm]
  have hpow : ((n : ℝ) ^ (-(line x t)).re) ^ 2 = (n : ℝ) ^ (-2 * x) := by
    simp only [neg_re, line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [hpow]
  congr 1
  simp only [Complex.normSq_apply, line, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    one_re, one_im, mul_zero, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  ring

/-- A common integrable square majorant for all closed strips in the right half-plane. -/
theorem diagonalVector_norm_sq_le (n : ℕ) (hn : 1 ≤ n) (x t : ℝ) (hx : 0 ≤ x) :
    ‖diagonalVector n (line x t)‖ ^ 2 ≤ (1 + t ^ 2)⁻¹ := by
  rw [diagonalVector_norm_sq n hn]
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hn' (show -2 * x ≤ 0 by linarith)
  have hd : 0 < (1 + x) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc
    _ ≤ 1 / ((1 + x) ^ 2 + t ^ 2) := div_le_div_of_nonneg_right hp hd.le
    _ ≤ 1 / (1 + t ^ 2) := div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith)
    _ = _ := one_div _

/-- Holomorphy and continuity of the diagonal vector on any closed positive strip. -/
theorem diagonalVector_regular {a b : ℝ} (ha : 0 ≤ a) (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableOn ℂ (diagonalVector n) (strip a b) ∧
    ContinuousOn (diagonalVector n) {s : ℂ | s.re ∈ Icc a b} := by
  have hf : Differentiable ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast (show n ≠ 0 by omega)))
  have hg : Differentiable ℂ (fun s : ℂ => 1 + s) := by fun_prop
  have hne (s : ℂ) (hs : a ≤ s.re) : 1 + s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at h'
    linarith
  exact ⟨hf.differentiableOn.div hg.differentiableOn (fun s hs => hne s hs.1.le),
    hf.continuous.continuousOn.div hg.continuous.continuousOn (fun s hs => hne s hs.1)⟩

/-- The actual diagonal function belongs to the Hardy space, with both exact boundary traces. -/
theorem diagonalVector_hardy_exists {a b : ℝ} (hab : a < b) (ha : 0 ≤ a)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : HardySpace a b, (∀ s ∈ strip a b, fourierLaplace d s = diagonalVector n s) ∧
      ((boundaryTraces hab d).1 =ᵐ[volume] fun t => diagonalVector n (line a t)) ∧
      ((boundaryTraces hab d).2 =ᵐ[volume] fun t => diagonalVector n (line b t)) := by
  have hr := diagonalVector_regular (b := b) ha n hn
  exact hardy_column_of_closedStrip_majorant hab hr.1 hr.2
    integrable_inv_one_add_sq (fun x hx t => diagonalVector_norm_sq_le n hn x t (ha.trans hx.1))

/-- The boundary square integral is evaluated exactly using the mass-one Poisson kernel. -/
theorem diagonalVector_line_integral (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : -1 < x) :
    (∫ t : ℝ, ‖diagonalVector n (line x t)‖ ^ 2) =
      Real.pi * ((n : ℝ) ^ (-2 * x) / (1 + x)) := by
  have hp : 0 < 1 + x := by linarith
  have heq (t : ℝ) : ‖diagonalVector n (line x t)‖ ^ 2 =
      (Real.pi * ((n : ℝ) ^ (-2 * x) / (1 + x))) * poissonKernelReal (1 + x) t := by
    rw [diagonalVector_norm_sq n hn]
    unfold poissonKernelReal
    field_simp [hp.ne', Real.pi_ne_zero]
  simp only [heq, integral_const_mul, (poissonKernelReal_integral (1 + x) hp).2, mul_one]

/-- The choice-based diagonal vector agrees with the actual Hardy representative. -/
theorem diagonalHardyVector_spec {a : ℝ} (ha : a < beta) (ha0 : 0 ≤ a) (n : ℕ) (hn : 1 ≤ n) :
    (∀ s ∈ strip a beta, fourierLaplace (diagonalHardyVector (a := a) n) s = diagonalVector n s) ∧
      ((boundaryTraces ha (diagonalHardyVector (a := a) n)).1 =ᵐ[volume]
        fun t => diagonalVector n (line a t)) ∧
      ((boundaryTraces ha (diagonalHardyVector (a := a) n)).2 =ᵐ[volume]
        fun t => diagonalVector n (line beta t)) := by
  obtain ⟨d, hd, hdl, hdr⟩ := diagonalVector_hardy_exists ha ha0 n hn
  have he : ∃ d : HardySpace a beta, ∀ s ∈ strip a beta,
      fourierLaplace d s = diagonalVector n s := ⟨d, hd⟩
  have hrep : ∀ s ∈ strip a beta,
      fourierLaplace (diagonalHardyVector (a := a) n) s = diagonalVector n s := by
    rw [diagonalHardyVector, dite_eq_left he]
    exact Classical.choose_spec he
  have heq : diagonalHardyVector (a := a) n = d :=
    fourierLaplace_injective_strip ha _ _ (fun s hs => (hrep s hs).trans (hd s hs).symm)
  exact ⟨hrep, by simpa only [heq] using hdl, by simpa only [heq] using hdr⟩

/-- The exact Hardy norm of the diagonal vector, including both boundary contributions. -/
theorem diagonalHardyVector_norm_sq {a : ℝ} (ha : a < beta) (ha0 : 0 ≤ a)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖diagonalHardyVector (a := a) n‖ ^ 2 = Real.pi *
      ((n : ℝ) ^ (-2 * a) / (1 + a) + (n : ℝ) ^ (-2 * beta) / (1 + beta)) := by
  have hs := diagonalHardyVector_spec ha ha0 n hn
  rw [boundaryTraces_norm_sq ha, l2_norm_sq_integral, l2_norm_sq_integral]
  have hleft := integral_congr_ae (hs.2.1.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  have hright := integral_congr_ae (hs.2.2.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  simp only [Function.comp_def] at hleft hright
  rw [hleft, hright,
    diagonalVector_line_integral n hn a (by linarith),
    diagonalVector_line_integral n hn beta (by norm_num [beta])]
  ring

/-- All five assertions about the diagonal vector in the audited statement of Proposition 6.5. -/
theorem proposition_6_5_diagonal_vector_spec (N : ℕ) [NeZero N] (_hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (ha : alpha N < beta) (n : ℕ) (hn : 1 ≤ n) :
    let d : HardySpace (alpha N) beta := diagonalHardyVector n
    (∀ s ∈ strip (alpha N) beta, fourierLaplace d s = diagonalVector n s) ∧
    ((boundaryTraces ha d).1 =ᵐ[volume] fun t : ℝ => diagonalVector n (line (alpha N) t)) ∧
    ((boundaryTraces ha d).2 =ᵐ[volume] fun t : ℝ => diagonalVector n (line beta t)) ∧
    ‖d‖ ^ 2 = Real.pi * (Real.rpow n (-2 * alpha N) / (1 + alpha N) +
      Real.rpow n (-2 * beta) / (1 + beta)) ∧
    (∀ h : HardySpace (alpha N) beta,
      InnerProductSpace.rankOne ℂ d d h = paperInner h d • d) := by
  have hN : 1 < (N : ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 10)).trans hlarge
  have ha0 : 0 ≤ alpha N := by unfold alpha; exact (div_pos zero_lt_one (Real.log_pos hN)).le
  have hs := diagonalHardyVector_spec ha ha0 n hn
  exact ⟨hs.1, hs.2.1, hs.2.2, diagonalHardyVector_norm_sq ha ha0 n hn,
    fun _ => InnerProductSpace.rankOne_apply _ _ _⟩

end ConditionalGoldbach
