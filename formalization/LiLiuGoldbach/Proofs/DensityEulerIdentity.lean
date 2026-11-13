import LiLiuGoldbach.Proofs.DensityArithmetic

/-! The exact Euler product identity and the complete density lemma. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff LSeries.notation
open MeasureTheory Filter Set Complex
namespace LiLiuGoldbach16
open MathlibNt.SieveTheory.SingularSeries hiding singularSeries
attribute [local instance] Classical.propDecidable

lemma density_prime_power_term (N p e : ℕ) (hp : p.Prime) (w : ℂ) (hw : w ≠ 0) :
    densityMultiplicativeTerm N w (p^(e+1)) =
      ((if 2 < p ∧ ¬p ∣ N then liuCorrectionFactor p else 1 : ℝ) : ℂ) *
        ((p : ℂ)^(-w))^(e+1) := by
  have hp0 : p^(e+1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [densityMultiplicativeTerm, ite_eq_right hp0,
    densityMultiplier_prime_pow N p (e+1) hp (by omega), div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  exact (riemannZetaSummandHom hw).map_pow p (e+1)

lemma density_prime_power_sum (N p : ℕ) (hp : p.Prime) {w : ℂ} (hw : 1 < w.re) :
    (∑' e : ℕ, densityMultiplicativeTerm N w (p^e)) =
      (1-(p : ℂ)^(-w))⁻¹ * (1+densityEulerTerm N p w) := by
  let q := (p : ℂ)^(-w)
  let c : ℂ := ((if 2 < p ∧ ¬p ∣ N then liuCorrectionFactor p else 1 : ℝ) : ℂ)
  have hw0 : w ≠ 0 := by intro he; norm_num [he] at hw
  have hq : ‖q‖ < 1 := by
    dsimp [q]
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hshift : HasSum (fun e : ℕ => densityMultiplicativeTerm N w (p^(e+1)))
      (c*q*(1-q)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one hq).mul_left (c*q) using 1
    ext e
    rw [density_prime_power_term N p e hp w hw0, pow_succ]
    dsimp [c, q]
    ring
  have hf : Summable (fun e : ℕ => densityMultiplicativeTerm N w (p^e)) :=
    (summable_nat_add_iff 1).mp hshift.summable
  rw [hf.tsum_eq_zero_add, pow_zero, densityMultiplicativeTerm_one, hshift.tsum_eq]
  have hqn : 1-q ≠ 0 := by
    intro he
    have : q = 1 := by linear_combination -he
    simpa [this] using hq
  by_cases hactive : 2 < p ∧ ¬p ∣ N
  · have hp2 : (2 : ℝ) < p := by exact_mod_cast hactive.1
    have hden : (p : ℂ)-2 ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    change 1+c*q*(1-q)⁻¹ = (1-q)⁻¹*(1+densityEulerTerm N p w)
    simp only [densityEulerTerm, hp, hactive.1, hactive.2, not_false_eq_true, and_self, ite_true,
      c, liuCorrectionFactor, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    change 1+((p : ℂ)-1)/((p : ℂ)-2)*q*(1-q)⁻¹ = (1-q)⁻¹*(1+q/((p : ℂ)-2))
    field_simp
    ring
  · have he : densityEulerTerm N p w = 0 := by simp [densityEulerTerm, hp, hactive]
    rw [he]
    change 1+c*q*(1-q)⁻¹ = (1-q)⁻¹*(1+0)
    simp only [c, ite_eq_right hactive, Complex.ofReal_one, one_mul, add_zero]
    field_simp
    ring

lemma densityMultiplier_eulerProduct (N : ℕ) (hN : Even N) (hpos : 0 < N)
    {w : ℂ} (hw : 1 < w.re) :
    (∑' k, densityMultiplicativeTerm N w k) = riemannZeta w * densityEulerProduct N w := by
  have hf := EulerProduct.eulerProduct_hasProd_mulIndicator
    (densityMultiplicativeTerm_one N w) (fun {k l} hkl => densityMultiplicativeTerm_mul N w hkl)
    (densityMultiplicativeTerm_summable_norm N hN hpos hw) (densityMultiplicativeTerm_zero N w)
  have hz : HasProd (fun p : ℕ => if p.Prime then (1-(p : ℂ)^(-w))⁻¹ else 1) (riemannZeta w) := by
    convert
      ((hasProd_subtype_iff_mulIndicator
        (f := fun p : ℕ => (1-(p : ℂ)^(-w))⁻¹) (s := {p : ℕ | p.Prime})).mp
          (riemannZeta_eulerProduct_hasProd hw)) using 1
    ext p
    by_cases hp : p.Prime <;> simp [Set.mulIndicator, hp]
  have he : HasProd (fun p => 1+densityEulerTerm N p w) (densityEulerProduct N w) := by
    rw [densityEulerProduct_eq_tprod]
    exact (multipliable_one_add_of_summable (densityEulerTerm_summable_norm N (by linarith))).hasProd
  apply hf.unique
  convert hz.mul he using 1
  ext p
  by_cases hp : p.Prime
  · simp only [Set.mulIndicator, Set.mem_setOf_eq, hp, ite_true,
      density_prime_power_sum N p hp hw]
  · simp [Set.mulIndicator, hp, densityEulerTerm]

lemma densitySeries_eq_continuedDensity (N : ℕ) (hN : Even N) (hpos : 0 < N)
    {w : ℂ} (hw : 1 < w.re) : densitySeries N w = continuedDensity N w := by
  rw [densitySeries_eq_multiplier_tsum N hpos w,
    densityMultiplier_eulerProduct N hN hpos hw]
  unfold continuedDensity
  ring

theorem lemma_4_3 (N : ℕ) (hN : Even N) (hN4 : 4 ≤ N) :
    (∀ w : ℂ, 0 < w.re → Summable (fun n : ℕ =>
      if 0 < n ∧ Nat.Coprime n N then ‖(mangoldt n : ℂ) ^ 2 / (n : ℂ) ^ (1 + w)‖ else 0)) ∧
    (∀ w : ℂ, 1 < w.re → densitySeries N w = continuedDensity N w) ∧
    MeromorphicOn (continuedDensity N) {w | 0 < w.re} ∧
    Tendsto (fun w : ℂ => (w - 1) * continuedDensity N w) (𝓝[≠] 1) (𝓝 ((N : ℂ) / N.totient)) ∧
    1 < singularSeries N ∧ C2 * N / N.totient ≤ singularSeries N ∧
    singularSeries N ≤ (N : ℝ) / N.totient := by
  exact ⟨fun w hw => diagonalSeries_summable N hw,
    fun w hw => densitySeries_eq_continuedDensity N hN (by omega) hw,
    continuedDensity_meromorphicOn N, continuedDensity_residue_one N hN (by omega),
    singularSeries_gt_one N, singularSeries_lower_totient N hN (by omega),
    singularSeries_upper_totient N hN (by omega)⟩

end LiLiuGoldbach16
