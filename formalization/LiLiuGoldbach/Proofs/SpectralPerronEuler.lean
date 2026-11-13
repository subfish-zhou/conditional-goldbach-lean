import LiLiuGoldbach.Proofs.SpectralPerronIntegral
import LiLiuGoldbach.Proofs.CharacterEulerBounds
import LiLiuGoldbach.Proofs.CharacterShortPolynomial

/-! The absolutely convergent finite Euler factors in the smoothed Perron integral. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace LiLiuGoldbach16
attribute [local instance] conductorNeZero

lemma perron_summable_coefficients {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    (a : ℕ → ℂ) (n : ℕ → ℕ) (hn : ∀ k, 0 < n k) (ha : Summable (fun k => ‖a k‖)) :
    Integrable (fun t : ℝ => (∑' k, a k*(n k : ℂ)^(-line c (2*Real.pi*t))) *
      smoothedPerronKernel X (line c (2*Real.pi*t))) ∧
    (∫ t : ℝ, (∑' k, a k*(n k : ℂ)^(-line c (2*Real.pi*t))) *
      smoothedPerronKernel X (line c (2*Real.pi*t))) =
      ∑' k, a k * (smoothedPerronWeight X (n k) : ℂ) ∧
    ‖∑' k, a k * (smoothedPerronWeight X (n k) : ℂ)‖ ≤ ∑' k, ‖a k‖ := by
  let v (t : ℝ) := line c (2*Real.pi*t)
  let F (k : ℕ) (t : ℝ) := a k * ((n k : ℂ)^(-v t) * smoothedPerronKernel X (v t))
  have hK : Integrable (fun t : ℝ => smoothedPerronKernel X (v t)) := by
    simpa only [Nat.cast_one,Complex.one_cpow,one_mul] using (perron_weight_integral hX hc 1 (by omega)).1
  have hf (k : ℕ) : Integrable (F k) := (perron_weight_integral hX hc (n k) (hn k)).1.const_mul (a k)
  have hbound (k : ℕ) (t : ℝ) : ‖F k t‖ ≤ ‖a k‖ * ‖smoothedPerronKernel X (v t)‖ := by
    have hpow : ‖(n k : ℂ)^(-v t)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (hn k)]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast hn k
      · simp only [v,line,neg_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
          mul_zero,zero_mul,sub_zero,add_zero]
        linarith
    dsimp [F]
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hpow) (norm_nonneg _)
  have hsi : Summable (fun k => ∫ t : ℝ, ‖F k t‖) := by
    apply (ha.mul_right (∫ t : ℝ, ‖smoothedPerronKernel X (v t)‖)).of_nonneg_of_le
    · intro k; exact integral_nonneg (fun t => norm_nonneg _)
    · intro k
      have hh := integral_mono (hf k).norm (hK.norm.const_mul ‖a k‖) (hbound k)
      simpa only [integral_const_mul] using hh
  have hsum (t : ℝ) : (∑' k, F k t) =
      (∑' k, a k*(n k : ℂ)^(-v t))*smoothedPerronKernel X (v t) := by
    simp only [F,← mul_assoc,tsum_mul_right]
  have hfin : Integrable (fun t : ℝ => ∑' k, F k t) := by
    apply (hK.norm.const_mul (∑' k, ‖a k‖)).mono'
      (AEStronglyMeasurable.tsum (fun k => (hf k).aestronglyMeasurable))
    filter_upwards [] with t
    have hs := (ha.mul_right ‖smoothedPerronKernel X (v t)‖).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound k t)
    exact (norm_tsum_le_tsum_norm hs).trans ((Summable.tsum_le_tsum (fun k => hbound k t) hs
      (ha.mul_right _)).trans_eq tsum_mul_right)
  refine ⟨by simpa only [hsum,v] using hfin,?_,?_⟩
  · rw [show (fun t : ℝ => (∑' k, a k*(n k : ℂ)^(-line c (2*Real.pi*t))) *
        smoothedPerronKernel X (line c (2*Real.pi*t))) = (fun t => ∑' k, F k t) by funext t; exact (hsum t).symm]
    rw [← integral_tsum_of_summable_integral_norm hf hsi]
    apply tsum_congr
    intro k
    exact (integral_const_mul _ _).trans (congrArg (fun z : ℂ => a k*z) (perron_weight_integral hX hc (n k) (hn k)).2)
  · have ht (k : ℕ) : ‖a k * (smoothedPerronWeight X (n k) : ℂ)‖ ≤ ‖a k‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (smoothedPerronWeight_nonneg_le_one hX _).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (smoothedPerronWeight_nonneg_le_one hX _).2
    have hs := ha.of_nonneg_of_le (fun k => norm_nonneg _) ht
    exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum ht hs ha)

lemma euler_geometric_ratio_norm_le {d : ℕ} [NeZero d] (χ : Character d)
    {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : 1/2 ≤ u.re) :
    ‖χ p/(p : ℂ)^u‖ ≤ 4/5 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hpow : (5/4 : ℝ) ≤ ‖(p : ℂ)^u‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    have hs : (5/4 : ℝ) ≤ Real.sqrt 2 := by
      have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hh' := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    calc
      (5/4 : ℝ) ≤ Real.sqrt 2 := hs
      _ = (2 : ℝ)^(1/2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ (p : ℝ)^(1/2 : ℝ) := Real.rpow_le_rpow (by norm_num) hp2 (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hu
  rw [norm_div]
  apply (div_le_div_of_nonneg_right (χ.norm_le_one p) (norm_nonneg _)).trans
  have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) (by norm_num : (0 : ℝ)<5/4) hpow
  norm_num at hh
  simpa only [one_div] using hh

lemma geometric_coefficients_norm_sum (q : ℂ) (hq : ‖q‖ ≤ 4/5) {L : ℝ} (hL : 0 ≤ L) :
    Summable (fun k : ℕ => ‖(L : ℂ)*q^(k+1)‖) ∧
      (∑' k : ℕ, ‖(L : ℂ)*q^(k+1)‖) ≤ 4*L := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hs := ((hasSum_geometric_of_lt_one (norm_nonneg q) hq1).mul_left ‖q‖).mul_left L
  have he (k : ℕ) : ‖(L : ℂ)*q^(k+1)‖ = L*(‖q‖*‖q‖^k) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL,norm_pow,pow_succ]
    ring
  have hs' : HasSum (fun k : ℕ => ‖(L : ℂ)*q^(k+1)‖) (L*(‖q‖*(1-‖q‖)⁻¹)) := by
    simpa only [he] using hs
  refine ⟨hs'.summable,?_⟩
  rw [hs'.tsum_eq]
  rw [mul_comm 4 L]
  apply mul_le_mul_of_nonneg_left _ hL
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 1-‖q‖)).mpr
  linarith

lemma euler_correction_geometric_series {d : ℕ} [NeZero d] (χ : Character d)
    {p : ℕ} (hp : p.Prime) {u v : ℂ} (hu : 1/2 ≤ u.re) (hv : 0 ≤ v.re) :
    (∑' k : ℕ, ((Real.log p : ℂ)*(χ p/(p : ℂ)^u)^(k+1)) *
      ((p^(k+1) : ℕ) : ℂ)^(-v)) = χ p*(Real.log p : ℂ)/((p : ℂ)^(u+v)-χ p) := by
  let q : ℂ := χ p/(p : ℂ)^u
  let r : ℂ := q*(p : ℂ)^(-v)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : (p : ℂ)^(u+v) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp0)
  have hq := euler_geometric_ratio_norm_le χ hp hu
  have hnorm : ‖(p : ℂ)^(-v)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_le) (by simpa using neg_nonpos.mpr hv)
  have hr : ‖r‖ < 1 := by
    have hh : ‖r‖ ≤ ‖q‖ := by dsimp [r]; rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hnorm
    exact hh.trans_lt (lt_of_le_of_lt hq (by norm_num))
  have hratio : r = χ p/(p : ℂ)^(u+v) := by
    dsimp [r,q]
    rw [Complex.cpow_add _ _ hp0,Complex.cpow_neg]
    ring
  have hne : 1-r ≠ 0 := by
    intro he
    have he' : r = 1 := by linear_combination -he
    simpa [he'] using hr
  have hden : (p : ℂ)^(u+v)-χ p ≠ 0 := by
    have he : (1-r)*(p : ℂ)^(u+v) = (p : ℂ)^(u+v)-χ p := by rw [hratio]; field_simp
    rw [← he]
    exact mul_ne_zero hne hpow
  have hterm (k : ℕ) : ((Real.log p : ℂ)*q^(k+1))*((p^(k+1) : ℕ) : ℂ)^(-v) =
      (Real.log p : ℂ)*r^(k+1) := by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]
    dsimp [r]
    rw [mul_pow]
    ring
  have hs : HasSum (fun k : ℕ => r^(k+1)) (r*(1-r)⁻¹) := by
    simpa only [pow_succ,mul_comm] using (hasSum_geometric_of_norm_lt_one hr).mul_left r
  simp_rw [show χ p/(p : ℂ)^u = q from rfl, hterm]
  rw [tsum_mul_left,hs.tsum_eq,hratio]
  field_simp [hpow,hden]

lemma euler_correction_term_perron {d : ℕ} [NeZero d] (χ : Character d)
    {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : 1/2 ≤ u.re)
    {X c : ℝ} (hX : 1 < X) (hc : 0 < c) :
    Integrable (fun t : ℝ =>
      (χ p*(Real.log p : ℂ)/((p : ℂ)^(u+line c (2*Real.pi*t))-χ p)) *
        smoothedPerronKernel X (line c (2*Real.pi*t))) ∧
      ‖∫ t : ℝ, (χ p*(Real.log p : ℂ)/((p : ℂ)^(u+line c (2*Real.pi*t))-χ p)) *
        smoothedPerronKernel X (line c (2*Real.pi*t))‖ ≤ 4*Real.log p := by
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hs := geometric_coefficients_norm_sum (χ p/(p : ℂ)^u) (euler_geometric_ratio_norm_le χ hp hu) hL
  have hh := perron_summable_coefficients hX hc
    (fun k => (Real.log p : ℂ)*(χ p/(p : ℂ)^u)^(k+1)) (fun k => p^(k+1))
    (fun k => pow_pos hp.pos _) hs.1
  have he (t : ℝ) := euler_correction_geometric_series χ hp hu
    (v := line c (2*Real.pi*t)) (by simpa [line] using hc.le)
  simp_rw [he] at hh
  refine ⟨hh.1,?_⟩
  rw [hh.2.1]
  exact hh.2.2.trans hs.2

lemma eulerCorrection_perron_integral {N : ℕ} [NeZero N] (χ : Character N)
    {u : ℂ} (hu : 1/2 ≤ u.re) {X c : ℝ} (hX : 1 < X) (hc : 0 < c) :
    Integrable (fun t : ℝ => eulerCorrection χ (u+line c (2*Real.pi*t)) *
      smoothedPerronKernel X (line c (2*Real.pi*t))) ∧
      ‖∫ t : ℝ, eulerCorrection χ (u+line c (2*Real.pi*t)) *
        smoothedPerronKernel X (line c (2*Real.pi*t))‖ ≤ 4*Real.log N := by
  classical
  let F (p : ℕ) (t : ℝ) := (if ¬p ∣ χ.conductor then
    χ.primitiveCharacter p*(Real.log p : ℂ)/((p : ℂ)^(u+line c (2*Real.pi*t))-χ.primitiveCharacter p) else 0) *
      smoothedPerronKernel X (line c (2*Real.pi*t))
  have hi (p : ℕ) (hp : p ∈ N.primeFactors) : Integrable (F p) := by
    by_cases hpc : p ∣ χ.conductor
    · simp [F,hpc]
    · simpa only [F,hpc,not_false_eq_true,ite_true] using
        (euler_correction_term_perron χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hu hX hc).1
  have he (t : ℝ) : eulerCorrection χ (u+line c (2*Real.pi*t)) *
      smoothedPerronKernel X (line c (2*Real.pi*t)) = ∑ p ∈ N.primeFactors, F p t := by
    simp only [eulerCorrection,F,Finset.sum_mul]
  constructor
  · simpa only [he] using integrable_finsetSum _ hi
  · simp_rw [he]
    rw [integral_finsetSum _ hi]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ p ∈ N.primeFactors, 4*Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hpc : p ∣ χ.conductor
        · simp [F,hpc]
          positivity
        · simpa only [F,hpc,not_false_eq_true,ite_true] using
            (euler_correction_term_perron χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hu hX hc).2
      _ = 4*(∑ p ∈ N.primeFactors, Real.log p) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_log_primeFactors_le_log N (NeZero.pos N)) (by norm_num)

lemma eulerCorrection_perron_error {N : ℕ} [NeZero N] (χ : Character N)
    {u : ℂ} (hu : 1/2 ≤ u.re) {X c : ℝ} (hX : 1 < X) (hc : 0 < c) :
    ‖eulerCorrection χ u - ∫ t : ℝ, eulerCorrection χ (u+line c (2*Real.pi*t)) *
      smoothedPerronKernel X (line c (2*Real.pi*t))‖ ≤ 8*Real.log N := by
  have h1 := eulerCorrection_norm_le χ hu
  have h2 := (eulerCorrection_perron_integral χ hu hX hc).2
  exact (norm_sub_le _ _).trans (by linarith)

end LiLiuGoldbach16
