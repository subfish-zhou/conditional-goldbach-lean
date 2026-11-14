module

public import ConditionalGoldbach.Proofs.HardyArithmeticTheorems
public import ConditionalGoldbach.Proofs.SpectralRankOneSeries
public import ConditionalGoldbach.Proofs.SpectralTraceBounds

/-! Hardy representatives of the finitely many logarithmic derivatives in the Gram kernel. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex InnerProductSpace
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma weighted_line_square_bound {x : ℝ} (hx : 0 ≤ x) (t L : ℝ) (hL : 0 ≤ L)
    (v : ℂ) (hv : ‖v‖ ≤ L * (1 + |t|) ^ (1 / 4 : ℝ)) :
    ‖v / (1 + line x t)‖ ^ 2 ≤ 4 * L ^ 2 * (1 + |t|) ^ (- (3 / 2 : ℝ)) := by
  have ht : 0 < 1 + |t| := by positivity
  have hl := one_add_line_norm_lower hx t
  have hb : ‖v / (1 + line x t)‖ ≤ 2 * L * (1 + |t|) ^ (- (3 / 4 : ℝ)) := by
    rw [norm_div]
    calc
      _ ≤ (L * (1 + |t|) ^ (1 / 4 : ℝ)) / ((1 + |t|) / 2) :=
        div_le_div₀ (by positivity) hv (by positivity) hl
      _ = _ := by
        rw [show - (3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub ht, Real.rpow_one]
        field_simp
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  have hp : ((1 + |t|) ^ (- (3 / 4 : ℝ))) ^ 2 = (1 + |t|) ^ (- (3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  simpa only [mul_pow, hp, show (2 : ℝ)^2 = 4 by norm_num] using hh

/-- The holomorphic function whose rank-one Gram sum is the arithmetic component. -/
def characterHardyFunction {N : ℕ} [NeZero N] (χ : Character N) (s : ℂ) : ℂ :=
  logDerivative χ s / (1 + s)

lemma characterHardyFunction_differentiableAt {N : ℕ} [NeZero N] (hGRH : GRH N)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (characterHardyFunction χ) s := by
  apply (odd_logDerivative_analyticAt_of_GRH hGRH χ hχ hs).differentiableAt.div (by fun_prop)
  intro he
  have hh := congrArg Complex.re he
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
  linarith

lemma characterHardyFunction_representation (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (ha : alpha N < beta)
    (χ : Character N) (hχ : χ ∈ oddCharacters N) :
    ∃ g : HardySpace (alpha N) beta,
      (∀ s ∈ strip (alpha N) beta, fourierLaplace g s = characterHardyFunction χ s) ∧
      ((boundaryTraces ha g).1 =ᵐ[volume] fun t => characterHardyFunction χ (line (alpha N) t)) ∧
      ((boundaryTraces ha g).2 =ᵐ[volume] fun t => characterHardyFunction χ (line beta t)) := by
  obtain ⟨L, _, hL, _, hlog, _⟩ := arithmeticKernel_growth_inputs N hlarge hGRH ha
  let A : ℝ := L * (64 * (2 * N) ^ (1 / 4 : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by have := (large_parameters hlarge).1; omega)
  have hd (s : ℂ) (hs : s.re ∈ Icc (alpha N) beta) :=
    characterHardyFunction_differentiableAt hGRH χ hχ ((large_alpha_pos hlarge).trans_le hs.1)
  apply hardy_column_of_closedStrip_majorant ha
    (fun s hs => (hd s ⟨hs.1.le, hs.2.le⟩).differentiableWithinAt)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (hardy_decay_integrable.const_mul (4 * A ^ 2))
  intro x hx t
  apply weighted_line_square_bound ((large_alpha_pos hlarge).le.trans hx.1) t A hA
  have hx' : (line x t).re ∈ Icc (alpha N) beta := by simpa [line] using hx
  have hh := hlog χ hχ (line x t) hx'
  simp only [line, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at hh
  apply hh.trans
  calc
    L * Real.log (N * (|t| + 2)) ^ 2 ≤
        L * ((64 * (2 * N) ^ (1 / 4 : ℝ)) * (1 + |t|) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (logarithm_square_le_quarter_power hN1 t) hL
    _ = A * (1 + |t|) ^ (1 / 4 : ℝ) := by dsimp [A]; ring

end ConditionalGoldbach
