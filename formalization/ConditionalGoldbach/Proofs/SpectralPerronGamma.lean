import ConditionalGoldbach.Proofs.SpectralPerronFubini
import ConditionalGoldbach.Proofs.GammaDifference

/-! Absolute summation of the Gamma resolvents in the smoothed Perron integral. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate BigOperators
namespace ConditionalGoldbach

lemma two_bounds_geometric_mean {d v m : ℝ} (hd : 0 ≤ d) (hv : 0 < v) (hm : 0 < m)
    (h1 : d ≤ 2/m) (h2 : d ≤ v/m^2) :
    d ≤ 2*v^(1/2 : ℝ)*m^(-(3/2 : ℝ)) := by
  have hh := mul_le_mul h1 h2 hd (by positivity : 0 ≤ 2/m)
  have hs : d^2 ≤ 2*v/m^3 := by convert hh using 1 <;> ring
  have hpv : (v^(1/2 : ℝ))^2 = v := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
    norm_num
  have hpm : (m^(-(3/2 : ℝ)))^2 = m⁻¹^3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num [Real.rpow_neg hm.le, inv_pow]
  apply (sq_le_sq₀ hd (by positivity)).mp
  rw [mul_pow,mul_pow,hpv,hpm]
  have hpos : 0 ≤ v/m^3 := by positivity
  simp only [inv_pow, ← div_eq_mul_inv]
  calc
    d^2 ≤ 2*(v/m^3) := by convert hs using 1 <;> ring
    _ ≤ 4*(v/m^3) := by nlinarith
    _ = _ := by ring

lemma gamma_perron_resolvent_bound {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    {u : ℂ} (hu : 1/2 ≤ u.re) (n : ℕ) (t : ℝ) :
    ‖smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((line c (2*Real.pi*t)+(u+1+2*(n : ℂ)))⁻¹-(u+1+2*(n : ℂ))⁻¹)‖ ≤
      (2*perronKernelNormConstant X c*(c⁻¹+(2*Real.pi)⁻¹)^(3/2 : ℝ)) *
        (((n : ℝ)+1)^(-(3/2 : ℝ)) * (1+|t|)^(-(3/2 : ℝ))) := by
  let v := line c (2*Real.pi*t)
  let a := u+1+2*(n : ℂ)
  let m : ℝ := (n : ℝ)+1
  have hm : 0 < m := by dsimp [m]; positivity
  have hAn : m ≤ ‖a‖ := by
    have hh := Complex.re_le_norm a
    have hre : a.re = u.re+1+2*(n : ℝ) := by simp [a]
    rw [hre] at hh
    dsimp [m]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hBn : m ≤ ‖v+a‖ := by
    have hh := Complex.re_le_norm (v+a)
    have hre : (v+a).re = c+(u.re+1+2*(n : ℝ)) := by simp [a,v,line]
    rw [hre] at hh
    dsimp [m]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hA : a ≠ 0 := norm_pos_iff.mp (hm.trans_le hAn)
  have hB : v+a ≠ 0 := norm_pos_iff.mp (hm.trans_le hBn)
  have hv : 0 < ‖v‖ := by
    have hh := Complex.re_le_norm v
    have hre : v.re = c := by simp [v,line]
    rw [hre] at hh
    exact hc.trans_le hh
  have h1 : ‖(v+a)⁻¹-a⁻¹‖ ≤ 2/m := by
    apply (norm_sub_le _ _).trans
    rw [norm_inv,norm_inv]
    have hh1 := inv_anti₀ hm hAn
    have hh2 := inv_anti₀ hm hBn
    simp only [div_eq_mul_inv]
    linarith
  have h2 : ‖(v+a)⁻¹-a⁻¹‖ ≤ ‖v‖/m^2 := by
    rw [inv_sub_inv' hB hA,show a-(v+a) = -v by ring,norm_mul,norm_mul,norm_neg,norm_inv,norm_inv]
    have hh1 := inv_anti₀ hm hAn
    have hh2 := inv_anti₀ hm hBn
    calc
      _ ≤ m⁻¹*‖v‖*m⁻¹ := by gcongr
      _ = _ := by ring
  have hmean := two_bounds_geometric_mean (norm_nonneg ((v+a)⁻¹-a⁻¹)) hv hm h1 h2
  have hK := smoothedPerronKernel_norm_bound hX c t
  have hN := perron_line_inverse_bound hc t
  have hC : 0 < c⁻¹+(2*Real.pi)⁻¹ := by positivity
  have hpow := Real.rpow_le_rpow (norm_nonneg (v⁻¹)) hN (by norm_num : (0 : ℝ) ≤ 3/2)
  have hid : ‖v⁻¹‖^2 * ‖v‖^(1/2 : ℝ) = ‖v⁻¹‖^(3/2 : ℝ) := by
    rw [norm_inv, ← Real.rpow_two, Real.inv_rpow (norm_nonneg v), ← Real.rpow_neg (norm_nonneg v),
      ← Real.rpow_add hv]
    norm_num
    rw [Real.inv_rpow (norm_nonneg v), Real.rpow_neg (norm_nonneg v)]
  rw [norm_mul]
  calc
    _ ≤ (perronKernelNormConstant X c*‖v⁻¹‖^2) * (2*‖v‖^(1/2 : ℝ)*m^(-(3/2 : ℝ))) :=
      mul_le_mul hK hmean (norm_nonneg _) (by have := (perronKernelNormConstant_pos hX c).le; positivity)
    _ = 2*perronKernelNormConstant X c*‖v⁻¹‖^(3/2 : ℝ)*m^(-(3/2 : ℝ)) := by
      calc
        _ = 2*perronKernelNormConstant X c*(‖v⁻¹‖^2*‖v‖^(1/2 : ℝ))*m^(-(3/2 : ℝ)) := by ring
        _ = _ := by rw [hid]
    _ ≤ 2*perronKernelNormConstant X c*((c⁻¹+(2*Real.pi)⁻¹)*(1+|t|)⁻¹)^(3/2 : ℝ)*m^(-(3/2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow
          (by have := (perronKernelNormConstant_pos hX c).le; positivity))
        (Real.rpow_nonneg hm.le _)
    _ = _ := by
      rw [Real.mul_rpow hC.le (by positivity),Real.inv_rpow (by positivity : 0 ≤ 1+|t|),
        ← Real.rpow_neg (by positivity : 0 ≤ 1+|t|)]
      dsimp [m]
      ring


lemma gamma_perron_resolvent_sum {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    {u : ℂ} (hu : 1/2 ≤ u.re) :
    Integrable (fun t : ℝ => ∑' n : ℕ, smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((line c (2*Real.pi*t)+(u+1+2*(n : ℂ)))⁻¹-(u+1+2*(n : ℂ))⁻¹)) ∧
    (∫ t : ℝ, ∑' n : ℕ, smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((line c (2*Real.pi*t)+(u+1+2*(n : ℂ)))⁻¹-(u+1+2*(n : ℂ))⁻¹)) =
      ∑' n : ℕ, smoothedPerronKernel X (-(u+1+2*(n : ℂ))) := by
  let F := fun (n : ℕ) (t : ℝ) => smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((line c (2*Real.pi*t)+(u+1+2*(n : ℂ)))⁻¹-(u+1+2*(n : ℂ))⁻¹)
  have ha (n : ℕ) : 0 < (u+1+2*(n : ℂ)).re := by
    simp only [add_re, mul_re, natCast_re, natCast_im]
    norm_num
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hF (n : ℕ) : Integrable (F n) :=
    (perron_resolvent_difference_integral hX hc (ha n)).1
  let B := 2*perronKernelNormConstant X c*(c⁻¹+(2*Real.pi)⁻¹)^(3/2 : ℝ)
  let I := ∫ t : ℝ, (1+|t|)^(-(3/2 : ℝ))
  have hw : Summable (fun n : ℕ => ((n : ℝ)+1)^(-(3/2 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(3/2 : ℝ))) 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num))
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    apply (hw.mul_left (B*I)).of_nonneg_of_le
      (fun n => integral_nonneg (fun t => norm_nonneg _))
    intro n
    calc
      _ ≤ ∫ t : ℝ, (B*((n : ℝ)+1)^(-(3/2 : ℝ)))*(1+|t|)^(-(3/2 : ℝ)) := by
        apply integral_mono (hF n).norm (hardy_decay_integrable.const_mul _)
        intro t
        simpa only [F, B, mul_assoc] using gamma_perron_resolvent_bound hX hc hu n t
      _ = _ := by rw [integral_const_mul]; dsimp [I]; ring
  refine ⟨integrable_tsum_of_summable_norm_integral hF hsum, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hF hsum]
  exact tsum_congr (fun n => (perron_resolvent_difference_integral hX hc (ha n)).2)

lemma gamma_half_difference_resolvents {u v : ℂ} (hu : 1/2 ≤ u.re) (hv : 0 ≤ v.re) :
    (logDeriv Gamma ((u+v+1)/2)-logDeriv Gamma ((u+1)/2))/2 =
      -(∑' n : ℕ, ((v+(u+1+2*(n : ℂ)))⁻¹-(u+1+2*(n : ℂ))⁻¹)) := by
  have hu' : 0 < ((u+v+1)/2).re := by simp; linarith
  have hv' : 0 < ((u+1)/2).re := by simp; linarith
  have h := (Gamma_logDeriv_difference_hasSum hu' hv').div_const (2 : ℂ)
  have he (n : ℕ) : (1/((u+1)/2+(n : ℂ))-1/((u+v+1)/2+(n : ℂ)))/2 =
      -((v+(u+1+2*(n : ℂ)))⁻¹-(u+1+2*(n : ℂ))⁻¹) := by
    have h1 : (u+1)/2+(n : ℂ) = (u+1+2*(n : ℂ))/2 := by ring
    have h2 : (u+v+1)/2+(n : ℂ) = (v+(u+1+2*(n : ℂ)))/2 := by ring
    rw [h1,h2]
    simp only [one_div, inv_div]
    ring
  simp_rw [he] at h
  exact h.tsum_eq.symm.trans tsum_neg

lemma gamma_perron_integral_eq {X c : ℝ} (hX : 1 < X) (hc : 0 < c)
    {u : ℂ} (hu : 1/2 ≤ u.re) :
    Integrable (fun t : ℝ => smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((logDeriv Gamma ((u+line c (2*Real.pi*t)+1)/2)-logDeriv Gamma ((u+1)/2))/2)) ∧
    (∫ t : ℝ, smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((logDeriv Gamma ((u+line c (2*Real.pi*t)+1)/2)-logDeriv Gamma ((u+1)/2))/2)) =
      -(∑' n : ℕ, smoothedPerronKernel X (-(u+1+2*(n : ℂ)))) := by
  have hh := gamma_perron_resolvent_sum hX hc hu
  have he (t : ℝ) : smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((logDeriv Gamma ((u+line c (2*Real.pi*t)+1)/2)-logDeriv Gamma ((u+1)/2))/2) =
      -(∑' n : ℕ, smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((line c (2*Real.pi*t)+(u+1+2*(n : ℂ)))⁻¹-(u+1+2*(n : ℂ))⁻¹)) := by
    rw [gamma_half_difference_resolvents hu (by simpa [line] using hc.le), mul_neg, tsum_mul_left]
  simp_rw [he]
  exact ⟨hh.1.neg, by rw [integral_neg, hh.2]⟩

lemma gamma_perron_kernel_bound {X : ℝ} (hX : 2 ≤ X) {u : ℂ}
    (hu : 1/2 ≤ u.re) (n : ℕ) :
    ‖smoothedPerronKernel X (-(u+1+2*(n : ℂ)))‖ ≤ 8/((n : ℝ)+1)^2 := by
  let a := u+1+2*(n : ℂ)
  have ha : (n : ℝ)+1 ≤ a.re := by simp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have han : (n : ℝ)+1 ≤ ‖a‖ := ha.trans (Complex.re_le_norm a)
  have hx : 1 < X := by linarith
  have hxs : 1 < Real.sqrt X := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hx)
  have hlog : 1/4 ≤ Real.log (Real.sqrt X) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX
    rw [Real.log_sqrt (by linarith : 0 ≤ X)]
    norm_num at h2
    linarith
  have hnum : ‖(X : ℂ)^(-a)-(Real.sqrt X : ℂ)^(-a)‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < X),
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Real.sqrt X)]
    have haneg : (-a).re ≤ 0 := by simp only [neg_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have h1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le haneg
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos hxs.le haneg
    linarith
  change ‖smoothedPerronKernel X (-a)‖ ≤ _
  unfold smoothedPerronKernel
  rw [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos hxs)]
  have hden : ((n : ℝ)+1)^2/4 ≤ ‖a‖^2*Real.log (Real.sqrt X) := by
    have hn := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ n+1) (norm_nonneg a) |>.mpr han
    nlinarith [mul_le_mul hn hlog (by norm_num : (0 : ℝ) ≤ 1/4) (sq_nonneg ‖a‖)]
  calc
    _ ≤ 2 / (((n : ℝ)+1)^2/4) :=
      div_le_div₀ (by norm_num) hnum (by positivity) hden
    _ = _ := by simp only [div_div_eq_mul_div]; ring

lemma gamma_perron_integral_bound {X c : ℝ} (hX : 2 ≤ X) (hc : 0 < c)
    {u : ℂ} (hu : 1/2 ≤ u.re) :
    Integrable (fun t : ℝ => smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((logDeriv Gamma ((u+line c (2*Real.pi*t)+1)/2)-logDeriv Gamma ((u+1)/2))/2)) ∧
    ‖∫ t : ℝ, smoothedPerronKernel X (line c (2*Real.pi*t)) *
      ((logDeriv Gamma ((u+line c (2*Real.pi*t)+1)/2)-logDeriv Gamma ((u+1)/2))/2)‖ ≤ 16 := by
  have hh := gamma_perron_integral_eq (by linarith : 1 < X) hc hu
  refine ⟨hh.1, ?_⟩
  rw [hh.2, norm_neg]
  have hs : Summable (fun n : ℕ => 1/((n : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => 1/(n : ℝ)^2) 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hK : Summable (fun n : ℕ => ‖smoothedPerronKernel X (-(u+1+2*(n : ℂ)))‖) :=
    (hs.mul_left 8).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by simpa only [mul_one_div] using gamma_perron_kernel_bound hX hu n)
  have hs2 : (∑' n : ℕ, 1/((n : ℝ)+1)^2) ≤ 2 := by
    apply le_of_tendsto hs.hasSum.tendsto_sum_nat
    exact Eventually.of_forall (fun n => (sum_one_div_nat_add_one_sq_le n).trans
      (by
        have hn : 0 ≤ 2/((n : ℝ)+1) := by positivity
        linarith))
  calc
    _ ≤ ∑' n : ℕ, ‖smoothedPerronKernel X (-(u+1+2*(n : ℂ)))‖ := norm_tsum_le_tsum_norm hK
    _ ≤ ∑' n : ℕ, 8*(1/((n : ℝ)+1)^2) :=
      hK.tsum_le_tsum (fun n => by simpa only [mul_one_div] using gamma_perron_kernel_bound hX hu n) (hs.mul_left 8)
    _ = 8*(∑' n : ℕ, 1/((n : ℝ)+1)^2) := tsum_mul_left
    _ ≤ 16 := by linarith

end ConditionalGoldbach
