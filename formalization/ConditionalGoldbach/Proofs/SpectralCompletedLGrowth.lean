module

public import Mathlib.Analysis.Real.Pi.Bounds
public import ConditionalGoldbach.Proofs.CharacterGrowthFoundation
public import ConditionalGoldbach.Proofs.CharacterZeroReflection
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! Growth of completed Dirichlet L-functions on expanding disks, from Euler's Gamma integral
and the primitive functional equation. -/
public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach

lemma gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans
  apply le_of_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.one_re]

lemma growth_scale_ge_one {R : ℝ} (hR : 1 ≤ R) : 1 ≤ R * Real.log (R + 2) := by
  have hlog : 1 ≤ Real.log (R + 2) := by
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  nlinarith

lemma gamma_right_disk_bound {R : ℝ} (hR : 1 ≤ R) {s : ℂ}
    (hslo : 1 / 4 ≤ s.re) (hshi : s.re ≤ R + 1) :
    ‖Gamma s‖ ≤ (Real.Gamma (1 / 4) + 1) * Real.exp (2 * R * Real.log (R + 2)) := by
  let n : ℕ := ⌈R⌉₊
  have hnlo : R ≤ (n : ℝ) := Nat.le_ceil R
  have hnhi : (n : ℝ) ≤ 2 * R := (Nat.ceil_lt_add_one (by linarith : 0 ≤ R)).le.trans (by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have hfact : (n.factorial : ℝ) ≤ Real.exp (2 * R * Real.log (R + 2)) := by
    have hpow : (n : ℝ)^n ≤ Real.exp (2 * R * Real.log (R + 2)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hnpos]
      apply Real.exp_le_exp.mpr
      have hnR : (n : ℝ) ≤ R + 2 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ R)).le.trans (by linarith)
      have hlog := Real.log_le_log hnpos hnR
      have hlogR : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      calc
        Real.log n * n ≤ Real.log (R + 2) * n := mul_le_mul_of_nonneg_right hlog hnpos.le
        _ ≤ Real.log (R + 2) * (2 * R) := mul_le_mul_of_nonneg_left hnhi hlogR
        _ = _ := by ring
    exact (show (n.factorial : ℝ) ≤ (n : ℝ)^n by exact_mod_cast Nat.factorial_le_pow n).trans hpow
  have hg : Real.Gamma s.re ≤ max (Real.Gamma (1 / 4)) (n.factorial : ℝ) := by
    have hh := Real.convexOn_Gamma.le_max_of_mem_Icc
      (show (1 / 4 : ℝ) ∈ Ioi 0 by norm_num)
      (show (n : ℝ) + 1 ∈ Ioi 0 by simp only [mem_Ioi]; positivity)
      (show s.re ∈ Icc (1 / 4) ((n : ℝ) + 1) by exact ⟨hslo, by linarith⟩)
    simpa only [Real.Gamma_nat_eq_factorial] using hh
  have hE : 1 ≤ Real.exp (2 * R * Real.log (R + 2)) :=
    Real.one_le_exp_iff.mpr (by nlinarith [growth_scale_ge_one hR])
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  calc
    _ ≤ Real.Gamma s.re := gamma_norm_le_real (by linarith)
    _ ≤ max (Real.Gamma (1 / 4)) (n.factorial : ℝ) := hg
    _ ≤ (Real.Gamma (1 / 4) + 1) * Real.exp (2 * R * Real.log (R + 2)) := by
      apply max_le
      · nlinarith
      · nlinarith

lemma gammaRealFactor_disk_bound {R : ℝ} (hR : 1 ≤ R) {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hshi : s.re ≤ R + 1) :
    ‖Gammaℝ s‖ ≤ (Real.Gamma (1 / 4) + 1) * Real.exp (2 * R * Real.log (R + 2)) := by
  have hpi : ‖(Real.pi : ℂ)^(-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [div_ofNat_re, neg_re]
    linarith
  rw [Complex.Gammaℝ_def, norm_mul]
  calc
    _ ≤ 1 * ‖Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact gamma_right_disk_bound hR (by simp only [div_ofNat_re]; linarith)
        (by simp only [div_ofNat_re]; linarith)

lemma gammaFactor_disk_bound {d : ℕ} (χ : Character d) {R : ℝ} (hR : 1 ≤ R) {s : ℂ}
    (hslo : 1 / 2 ≤ s.re) (hsnorm : ‖s‖ ≤ R) :
    ‖χ.gammaFactor s‖ ≤ (Real.Gamma (1 / 4) + 1) * Real.exp (2 * R * Real.log (R + 2)) := by
  have hsre : s.re ≤ R := (Complex.re_le_norm s).trans hsnorm
  classical
  simp only [DirichletCharacter.gammaFactor]
  split_ifs
  · exact gammaRealFactor_disk_bound hR hslo (by linarith)
  · exact gammaRealFactor_disk_bound hR (by simp only [add_re, one_re]; linarith)
      (by simp only [add_re, one_re]; linarith)

lemma completedLFunction_right_disk_bound {d : ℕ} [NeZero d] (χ : Character d) (hχ : χ ≠ 1)
    {R : ℝ} (hR : 1 ≤ R) {s : ℂ} (hslo : 1 / 2 ≤ s.re) (hsnorm : ‖s‖ ≤ R) :
    ‖χ.completedLFunction s‖ ≤
      (3 * d * (Real.Gamma (1 / 4) + 1)) * Real.exp (3 * R * Real.log (R + 2)) := by
  have hspos : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by intro he; simp [he] at hspos
  have hL : ‖χ.LFunction s‖ ≤ (d : ℝ) * (1 + 2 * R) := by
    apply (LFunction_polynomial_bound χ hχ s hspos).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply add_le_add le_rfl
    calc
      ‖s‖ / s.re ≤ R / (1 / 2 : ℝ) := div_le_div₀ (by linarith) hsnorm (by norm_num) hslo
      _ = _ := by ring
  have hE : 1 + 2 * R ≤ 3 * Real.exp (R * Real.log (R + 2)) := by
    have he : R + 2 ≤ Real.exp (R * Real.log (R + 2)) := by
      calc
        R + 2 = Real.exp (Real.log (R + 2)) := (Real.exp_log (by linarith)).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg (show 1 ≤ R + 2 by linarith)])
    linarith
  have heq : χ.completedLFunction s = χ.LFunction s * χ.gammaFactor s := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hsne)]
    exact (div_mul_cancel₀ _ (gammaFactor_ne_zero_re_pos χ hspos)).symm
  rw [heq, norm_mul]
  calc
    _ ≤ ((d : ℝ) * (1 + 2 * R)) *
        ((Real.Gamma (1 / 4) + 1) * Real.exp (2 * R * Real.log (R + 2))) :=
      mul_le_mul hL (gammaFactor_disk_bound χ hR hslo hsnorm) (norm_nonneg _)
        (by positivity)
    _ ≤ ((d : ℝ) * (3 * Real.exp (R * Real.log (R + 2)))) *
        ((Real.Gamma (1 / 4) + 1) * Real.exp (2 * R * Real.log (R + 2))) := by
      gcongr
    _ = _ := by
      rw [show (d : ℝ) * (3 * Real.exp (R * Real.log (R + 2))) *
        ((Real.Gamma (1 / 4) + 1) * Real.exp (2 * R * Real.log (R + 2))) =
        (3 * d * (Real.Gamma (1 / 4) + 1)) *
        (Real.exp (R * Real.log (R + 2)) * Real.exp (2 * R * Real.log (R + 2))) by ring,
        ← Real.exp_add]
      congr 2
      ring

lemma growth_scale_successor {R : ℝ} (hR : 1 ≤ R) :
    (R + 1) * Real.log (R + 3) ≤ 4 * (R * Real.log (R + 2)) := by
  have hl0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hl : Real.log (R + 3) ≤ 2 * Real.log (R + 2) := by
    have hh := Real.log_le_log (show 0 < R + 3 by linarith)
      (show R + 3 ≤ (R + 2) * (R + 2) by nlinarith)
    rw [Real.log_mul (by linarith : R + 2 ≠ 0) (by linarith : R + 2 ≠ 0)] at hh
    linarith
  calc
    _ ≤ (R + 1) * (2 * Real.log (R + 2)) := mul_le_mul_of_nonneg_left hl (by linarith)
    _ ≤ (2 * R) * (2 * Real.log (R + 2)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- The completed primitive L-function has order at most one, with the precise
`exp (A R log(R+2))` majorant needed for the Hadamard argument. -/
theorem completedLFunction_disk_growth {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 1 ≤ R → ∀ s : ℂ, ‖s‖ ≤ R →
      ‖χ.completedLFunction s‖ ≤ Real.exp (A * R * Real.log (R + 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdlog : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  let K₀ : ℝ := 3 * d * (Real.Gamma (1 / 4) + 1)
  let K : ℝ := K₀ * (‖χ.rootNumber‖ + 1)
  let B : ℝ := 12 + 2 * Real.log d
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B + |Real.log K| + 1, by positivity, ?_⟩
  intro R hR s hs
  let X := R * Real.log (R + 2)
  have hX : 1 ≤ X := growth_scale_ge_one hR
  have hXR : R ≤ X := by
    have hl : 1 ≤ Real.log (R + 2) := by
      apply (Real.le_log_iff_exp_le (by linarith)).mpr
      exact Real.exp_one_lt_three.le.trans (by linarith)
    dsimp [X]
    nlinarith
  have hbasic : ‖χ.completedLFunction s‖ ≤ K * Real.exp (B * X) := by
    by_cases hre : 1 / 2 ≤ s.re
    · have hh := completedLFunction_right_disk_bound χ hχ hR hre hs
      apply hh.trans
      apply mul_le_mul
      · dsimp [K]
        nlinarith [norm_nonneg χ.rootNumber]
      · apply Real.exp_le_exp.mpr
        dsimp [B, X]
        have hx0 : 0 ≤ R * Real.log (R + 2) := le_trans (by norm_num) hX
        nlinarith [mul_nonneg hdlog hx0]
      · positivity
      · exact hK.le
    · have hright : 1 / 2 ≤ (1 - s).re := by simp; linarith
      have hnorm : ‖1 - s‖ ≤ R + 1 := by
        have hh := (norm_sub_le (1 : ℂ) s).trans (add_le_add le_rfl hs)
        simpa only [norm_one, add_comm] using hh
      have hh := completedLFunction_right_disk_bound χ⁻¹ (inv_ne_one.mpr hχ)
        (show 1 ≤ R + 1 by linarith) hright hnorm
      have hright' : ‖χ⁻¹.completedLFunction (1 - s)‖ ≤ K₀ * Real.exp (12 * X) := by
        apply hh.trans
        apply mul_le_mul_of_nonneg_left _ hK₀.le
        apply Real.exp_le_exp.mpr
        have ht := growth_scale_successor hR
        dsimp [X]
        convert mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 3 by norm_num) using 1 <;> ring_nf
      have hpower : ‖(d : ℂ)^((1 - s) - 1 / 2)‖ ≤ Real.exp ((2 * Real.log d) * X) := by
        rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne d)),
          Real.rpow_def_of_pos hd0]
        apply Real.exp_le_exp.mpr
        have hneg : -s.re ≤ R := (neg_le_abs s.re).trans ((Complex.abs_re_le_norm s).trans hs)
        simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re] at *
        calc
          Real.log d * (1 - s.re - 1 / 2) ≤ Real.log d * (2 * R) :=
            mul_le_mul_of_nonneg_left (by linarith) hdlog
          _ ≤ Real.log d * (2 * X) := mul_le_mul_of_nonneg_left (by linarith) hdlog
          _ = _ := by ring
      have heq := hprim.completedLFunction_one_sub (1 - s)
      rw [sub_sub_cancel] at heq
      rw [heq, norm_mul, norm_mul]
      calc
        _ ≤ Real.exp ((2 * Real.log d) * X) * (‖χ.rootNumber‖ + 1) *
            (K₀ * Real.exp (12 * X)) := by
          gcongr
          exact le_add_of_nonneg_right zero_le_one
        _ = K * Real.exp (B * X) := by
          dsimp [K, B]
          rw [show Real.exp ((2 * Real.log d) * X) * (‖χ.rootNumber‖ + 1) *
            (K₀ * Real.exp (12 * X)) =
            K₀ * (‖χ.rootNumber‖ + 1) *
              (Real.exp ((2 * Real.log d) * X) * Real.exp (12 * X)) by ring,
            ← Real.exp_add]
          congr 2
          ring
  apply hbasic.trans
  calc
    K * Real.exp (B * X) = Real.exp (Real.log K + B * X) := by
      rw [Real.exp_add, Real.exp_log hK]
    _ ≤ Real.exp ((B + |Real.log K| + 1) * R * Real.log (R + 2)) := by
      apply Real.exp_le_exp.mpr
      have hh : Real.log K ≤ |Real.log K| * X := by
        exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hX)
      dsimp [X] at *
      nlinarith

/-- The same disk estimate in the paper's conductor-normalized convention. -/
theorem completedL_disk_growth {d : ℕ} [NeZero d] (χ : Character d)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 1 ≤ R → ∀ s : ℂ, ‖s‖ ≤ R →
      ‖completedL χ s‖ ≤ Real.exp (A * R * Real.log (R + 2)) := by
  obtain ⟨A, hA, hbound⟩ := completedLFunction_disk_growth χ hχ hprim
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hdlog : 0 ≤ Real.log d := Real.log_nonneg
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  refine ⟨A + Real.log d, by positivity, ?_⟩
  intro R hR s hs
  have hlogR : 1 ≤ Real.log (R + 2) := by
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hpower : ‖(d : ℂ)^((s + 1) / 2)‖ ≤ Real.exp (Real.log d * R * Real.log (R + 2)) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne d)),
      Real.rpow_def_of_pos hd0]
    apply Real.exp_le_exp.mpr
    have hsre : s.re ≤ R := (Complex.re_le_norm s).trans hs
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    calc
      Real.log d * ((s.re + 1) / 2) ≤ Real.log d * R :=
        mul_le_mul_of_nonneg_left (by linarith) hdlog
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hlogR
  rw [completedL, norm_mul]
  calc
    _ ≤ Real.exp (Real.log d * R * Real.log (R + 2)) * Real.exp (A * R * Real.log (R + 2)) :=
      mul_le_mul hpower (hbound R hR s hs) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end ConditionalGoldbach
