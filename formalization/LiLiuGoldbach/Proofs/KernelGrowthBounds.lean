import LiLiuGoldbach.Proofs.GammaQuotientBound
import LiLiuGoldbach.Proofs.ZetaGrowth
import LiLiuGoldbach.Proofs.Elementary

/-! Quantitative component bounds for the Hardy kernel on a fixed closed strip. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16

lemma logarithm_square_le_quarter_power {n : ℝ} (hn : 1 ≤ n) (t : ℝ) :
    Real.log (n * (|t| + 2)) ^ 2 ≤
      (64 * (2 * n) ^ (1 / 4 : ℝ)) * (1 + |t|) ^ (1 / 4 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hx : 1 ≤ n * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hlog := Real.log_le_rpow_div (by positivity : 0 ≤ n * (|t| + 2))
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hs := (sq_le_sq₀ (Real.log_nonneg hx) (by positivity)).mpr hlog
  have hp : (n * (|t| + 2)) ^ (1 / 4 : ℝ) ≤
      ((2 * n) * (1 + |t|)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t]) (by norm_num)
  have he : ((n * (|t| + 2)) ^ (1 / 8 : ℝ) / (1 / 8)) ^ 2 =
      64 * (n * (|t| + 2)) ^ (1 / 4 : ℝ) := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    ring
  rw [he] at hs
  calc
    _ ≤ 64 * (n * (|t| + 2)) ^ (1 / 4 : ℝ) := hs
    _ ≤ 64 * (((2 * n) * (1 + |t|)) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

lemma diagonalSeries_uniform_bound (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, a ≤ w.re → ‖diagonalSeries N w‖ ≤ D := by
  let d : ℕ → ℝ := fun n => if 0 < n ∧ Nat.Coprime n N then
    ‖(mangoldt n : ℂ)^2 / (n : ℂ)^(1+(a : ℂ))‖ else 0
  have hd : Summable d := diagonalSeries_summable N (by simpa using ha)
  refine ⟨∑' n, d n, tsum_nonneg (fun n => by dsimp [d]; split_ifs <;> positivity), ?_⟩
  intro w hw
  have hw0 : 0 < w.re := ha.trans_le hw
  have hs : Summable (fun n : ℕ => if 0 < n ∧ Nat.Coprime n N then
      (mangoldt n : ℂ)^2 / (n : ℂ)^(1+w) else 0) := by
    apply summable_norm_iff.mp
    simpa only [apply_ite norm, norm_zero] using diagonalSeries_summable N hw0
  apply (norm_tsum_le_tsum_norm hs.norm).trans
  apply Summable.tsum_le_tsum _ hs.norm hd
  intro n
  by_cases hn : 0 < n ∧ Nat.Coprime n N
  · simp only [d, if_pos hn, norm_div]
    apply div_le_div_of_nonneg_left (norm_nonneg _)
      (Complex.norm_natCast_cpow_pos_of_pos hn.1 _)
    rw [Complex.norm_natCast_cpow_of_pos hn.1, Complex.norm_natCast_cpow_of_pos hn.1]
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hn.1
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith
  · simp [hn, d]

lemma characterKernel_power_bound {a b : ℝ} (N : ℕ) [NeZero N] (L : ℝ) (hL : 0 ≤ L)
    (hlog : ∀ χ ∈ oddCharacters N, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖logDerivative χ s‖ ≤ L * (1 + |s.im|) ^ (1 / 4 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s z : ℂ, s.re ∈ Icc a b → z.re ∈ Icc a b →
      ‖characterKernel N s (conj z)‖ ≤
        C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) := by
  let A : ℝ := ‖(2 : ℂ) / N.totient‖
  refine ⟨A * (oddCharacters N).card * L ^ 2, by dsimp [A]; positivity, ?_⟩
  intro s z hs hz
  simp only [characterKernel, Complex.conj_conj, norm_mul]
  calc
    A * ‖∑ χ ∈ oddCharacters N, logDerivative χ s * conj (logDerivative χ z)‖ ≤
        A * ∑ χ ∈ oddCharacters N, ‖logDerivative χ s * conj (logDerivative χ z)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ A * ∑ _χ ∈ oddCharacters N,
        (L * (1 + |s.im|) ^ (1 / 4 : ℝ)) * (L * (1 + |z.im|) ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hlog χ hχ s hs) (hlog χ hχ z hz) (norm_nonneg _) (by positivity)
    _ = _ := by rw [Finset.sum_const]; simp only [nsmul_eq_mul]; ring

lemma one_add_line_norm_lower {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    (1 + |t|) / 2 ≤ ‖1 + line x t‖ := by
  have hr := Complex.abs_re_le_norm (1 + line x t)
  have hi := Complex.abs_im_le_norm (1 + line x t)
  simp only [line, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero, Complex.add_im, Complex.one_im,
    Complex.mul_im, mul_one, zero_add] at hr hi
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 + x)] at hr
  unfold line
  linarith

lemma weightedKernel_power_bound_of_residual {a b : ℝ} (ha : 0 ≤ a)
    (N : ℕ) [NeZero N] (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ s z : ℂ, s.re ∈ Icc a b → z.re ∈ Icc a b →
      ‖residual N s (conj z)‖ ≤
        C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ)) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ∀ v t : ℝ,
      ‖weightedKernel N (line x v) (line y t)‖ ^ 2 ≤
        (16 * C ^ 2) * (1 + |v|) ^ (- (3 / 2 : ℝ)) *
          (1 + |t|) ^ (- (3 / 2 : ℝ)) := by
  intro x hx y hy v t
  have hv0 : 0 < 1 + |v| := by positivity
  have ht0 : 0 < 1 + |t| := by positivity
  have hvl := one_add_line_norm_lower (ha.trans hx.1) v
  have htl := one_add_line_norm_lower (ha.trans hy.1) t
  have hR' : ‖residual N (line x v) (conj (line y t))‖ ≤
      C * (1 + |v|) ^ (1 / 4 : ℝ) * (1 + |t|) ^ (1 / 4 : ℝ) := by
    simpa [line] using hR (line x v) (line y t) (by simpa [line] using hx) (by simpa [line] using hy)
  have hnorm : ‖weightedKernel N (line x v) (line y t)‖ ≤
      (4 * C) * (1 + |v|) ^ (- (3 / 4 : ℝ)) * (1 + |t|) ^ (- (3 / 4 : ℝ)) := by
    rw [weightedKernel, norm_div, norm_mul]
    have hc : ‖1 + conj (line y t)‖ = ‖1 + line y t‖ := by
      simpa only [map_add, map_one] using Complex.norm_conj (1 + line y t)
    rw [hc]
    calc
      _ ≤ (C * (1 + |v|) ^ (1 / 4 : ℝ) * (1 + |t|) ^ (1 / 4 : ℝ)) /
          (((1 + |v|) / 2) * ((1 + |t|) / 2)) :=
        div_le_div₀ (by positivity) hR' (by positivity)
          (mul_le_mul hvl htl (by positivity) (norm_nonneg _))
      _ = _ := by
        have hv : (1 + |v|) ^ (- (3 / 4 : ℝ)) =
            (1 + |v|) ^ (1 / 4 : ℝ) / (1 + |v|) := by
          rw [show - (3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub hv0, Real.rpow_one]
        have ht : (1 + |t|) ^ (- (3 / 4 : ℝ)) =
            (1 + |t|) ^ (1 / 4 : ℝ) / (1 + |t|) := by
          rw [show - (3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub ht0, Real.rpow_one]
        rw [hv, ht]
        field_simp <;> ring
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have hp (u : ℝ) (hu : 0 < 1 + |u|) :
      ((1 + |u|) ^ (- (3 / 4 : ℝ))) ^ 2 = (1 + |u|) ^ (- (3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    norm_num
  simpa only [mul_pow, hp v hv0, hp t ht0, show (4 : ℝ)^2 = 16 by norm_num] using hsq

lemma continuedModel_power_bound {a : ℝ} (ha : 0 < a) (hab : a < beta)
    (N : ℕ) (hN : 4 ≤ N) (Z : ℝ) (hZ : 0 ≤ Z)
    (hζ : ∀ w : ℂ, w.re ∈ Icc (3 / 4) (1 - 2 * a) →
      ‖riemannZeta w‖ ≤ Z * (1 + |w.im|) ^ (1 / 4 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s z : ℂ, s.re ∈ Icc a beta → z.re ∈ Icc a beta →
      ‖continuedModel N s (conj z)‖ ≤
        C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) := by
  obtain ⟨G, hG, hGamma⟩ := gammaQuotient_uniform_bound ha (by norm_num [beta] : beta < 3 / 2)
  let E : ℝ := Real.exp (∑' p : ℕ, 3 * ‖LSeries.term 1 (1 + ((2 * a : ℝ) : ℂ)) p‖)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hS : 0 ≤ singularSeries N := (singularSeries_pos N).le
  refine ⟨singularSeries N * E * Z * G ^ 2, by positivity, ?_⟩
  intro s z hs hz
  have hw : 2 * a ≤ (s + conj z).re := by simp; linarith [hs.1, hz.1]
  have hEuler : ‖densityEulerProduct N (s + conj z)‖ ≤ E :=
    densityEulerProduct_uniform_bound (by positivity) N hw
  have hpow : ‖((Real.pi : ℂ) / N) ^ (s + conj z)‖ ≤ 1 := by
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [show (Real.pi : ℂ) / N = ((Real.pi / (N : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos Real.pi_pos hn)]
    apply Real.rpow_le_one (by positivity)
    · apply (div_le_one hn).mpr
      have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
      linarith [Real.pi_lt_four]
    · exact (by positivity : (0 : ℝ) ≤ 2 * a).trans hw
  have hzet : ‖riemannZeta (1 - s - conj z)‖ ≤
      Z * ((1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ)) := by
    have hw' : (1 - s - conj z).re ∈ Icc (3 / 4) (1 - 2 * a) := by
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      constructor <;> dsimp [beta] at hs hz <;> linarith [hs.1, hs.2, hz.1, hz.2]
    apply (hζ _ hw').trans
    apply mul_le_mul_of_nonneg_left _ hZ
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have he : (1 - s - conj z).im = -(s.im - z.im) := by simp; ring
    rw [he, abs_neg]
    have hh := abs_sub s.im z.im
    nlinarith [mul_nonneg (abs_nonneg s.im) (abs_nonneg z.im)]
  have hGammaS := hGamma s hs
  have hGammaZ := hGamma (conj z) (by simpa using hz)
  simp only [continuedModel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
  calc
    singularSeries N * ‖((Real.pi : ℂ) / N) ^ (s + conj z)‖ *
        ‖densityEulerProduct N (s + conj z)‖ * ‖riemannZeta (1 - s - conj z)‖ *
        ‖gammaQuotient s‖ * ‖gammaQuotient (conj z)‖ ≤
      singularSeries N * 1 * E *
        (Z * ((1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ))) * G * G := by
      gcongr
    _ = _ := by ring

lemma residual_power_bound_of_components {a b : ℝ} (ha : 0 < a)
    (N : ℕ) [NeZero N] (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hchar : ∀ s z : ℂ, s.re ∈ Icc a b → z.re ∈ Icc a b →
      ‖characterKernel N s (conj z)‖ ≤
        P * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ))
    (hmodel : ∀ s z : ℂ, s.re ∈ Icc a b → z.re ∈ Icc a b →
      ‖continuedModel N s (conj z)‖ ≤
        Q * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s z : ℂ, s.re ∈ Icc a b → z.re ∈ Icc a b →
      ‖residual N s (conj z)‖ ≤
        C * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) := by
  obtain ⟨D, hD, hdiag⟩ := diagonalSeries_uniform_bound N (by positivity : 0 < 2 * a)
  refine ⟨P + D + Q, by positivity, ?_⟩
  intro s z hs hz
  have hS : 1 ≤ (1 + |s.im|) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by norm_num)
  have hT : 1 ≤ (1 + |z.im|) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg z.im]) (by norm_num)
  have hd : ‖diagonalSeries N (s + conj z)‖ ≤
      D * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) := by
    apply (hdiag _ (by simp; linarith [hs.1, hz.1])).trans
    calc
      D = D * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ‖characterKernel N s (conj z)‖ + ‖diagonalSeries N (s + conj z)‖ +
        ‖continuedModel N s (conj z)‖ := by
      unfold residual
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ P * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) +
        D * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) +
        Q * (1 + |s.im|) ^ (1 / 4 : ℝ) * (1 + |z.im|) ^ (1 / 4 : ℝ) :=
      add_le_add (add_le_add (hchar s z hs hz) hd) (hmodel s z hs hz)
    _ = _ := by ring

end LiLiuGoldbach16
