import ConditionalGoldbach.Proofs.ResidualAnalytic
import ConditionalGoldbach.Proofs.Elementary

/-! The complete strip geometry and the holomorphic/antiholomorphic kernel interface. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable conductorNeZero

lemma analyticDomain_isOpen : IsOpen analyticDomain := by
  unfold analyticDomain
  exact (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
    ((isOpen_lt (Complex.continuous_re.comp continuous_fst) continuous_const).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)).inter
        (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const)))

lemma weightedKernel_hermitian (N : ℕ) [NeZero N] : HermitianKernel (weightedKernel N) := by
  intro s z
  unfold weightedKernel
  rw [map_div₀, map_mul, map_add, map_add, map_one, residual_conj, Complex.conj_conj,
    residual_symmetric]
  congr 1
  ring

lemma weightedKernel_conj_differentiableOn (N : ℕ) [NeZero N] (hN : 0 < N) (hGRH : GRH N) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => weightedKernel N p.1 (conj p.2)) analyticDomain := by
  have hr := residual_differentiableOn N hN hGRH
  intro p hp
  have hs : (1 : ℂ)+p.1 ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [add_re, one_re, zero_re] at he'
    linarith [hp.1]
  have hz : (1 : ℂ)+p.2 ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [add_re, one_re, zero_re] at he'
    linarith [hp.2.2.1]
  simp only [weightedKernel, Complex.conj_conj]
  have hd : DifferentiableWithinAt ℂ (fun q : ℂ × ℂ => (1+q.1)*(1+q.2)) analyticDomain p := by fun_prop
  simpa only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using! (hr p hp).mul (hd.inv (mul_ne_zero hs hz))

lemma hasDerivAt_real_affine_comp {f : ℂ → ℂ} {s : ℂ}
    (hf : DifferentiableAt ℂ f s) (v : ℂ) :
    HasDerivAt (fun x : ℝ => f (s+x*v)) (deriv f s*v) 0 := by
  have hf' : HasDerivAt f (deriv f s) (s+(0 : ℂ)*v) := by simpa using hf.hasDerivAt
  have h := hf'.comp 0 (((hasDerivAt_id (0 : ℂ)).mul_const v).const_add s)
  simpa using h.comp_ofReal

lemma wirtingerBar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {s : ℂ}
    (hf : DifferentiableAt ℂ f s) : wirtingerBar f s = 0 := by
  have hx := (hasDerivAt_real_affine_comp hf 1).deriv
  simp only [mul_one] at hx
  have hy := (hasDerivAt_real_affine_comp hf I).deriv
  rw [wirtingerBar, hx, hy]
  have hI := Complex.I_sq
  linear_combination (deriv f s/2)*hI

lemma wirtinger_comp_conj_eq_zero {f : ℂ → ℂ} {s : ℂ}
    (hf : DifferentiableAt ℂ f (conj s)) : wirtinger (fun z => f (conj z)) s = 0 := by
  have hx := (hasDerivAt_real_affine_comp hf 1).deriv
  simp only [mul_one] at hx
  have hy := (hasDerivAt_real_affine_comp hf (-I)).deriv
  simp only [wirtinger, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, hx, hy]
  have hI := Complex.I_sq
  linear_combination (deriv f (conj s)/2)*hI

lemma residual_wirtinger (N : ℕ) [NeZero N] (hN : 0 < N) (hGRH : GRH N)
    (s z : ℂ) (hp : (s,conj z) ∈ analyticDomain) :
    wirtingerBar (fun w => residual N w (conj z)) s = 0 ∧
    wirtinger (fun w => residual N s (conj w)) z = 0 := by
  have hr : DifferentiableAt ℂ (fun p : ℂ × ℂ => residual N p.1 p.2) (s,conj z) :=
    (residual_differentiableOn N hN hGRH).differentiableAt (analyticDomain_isOpen.mem_nhds hp)
  constructor
  · exact wirtingerBar_eq_zero_of_differentiableAt
      (DifferentiableAt.comp (g := fun p : ℂ × ℂ => residual N p.1 p.2)
        (f := fun w : ℂ => (w,conj z)) s hr (by fun_prop))
  · exact wirtinger_comp_conj_eq_zero
      (DifferentiableAt.comp (g := fun p : ℂ × ℂ => residual N p.1 p.2)
        (f := fun w : ℂ => (s,w)) (conj z) hr (by fun_prop))

lemma large_alpha_pos {N : ℕ} (hlarge : Real.exp 10 < (N : ℝ)) : 0 < alpha N :=
  one_div_pos.mpr (large_parameters hlarge).2.1

lemma large_closed_strip_subset {N : ℕ} (hlarge : Real.exp 10 < (N : ℝ)) :
    {p : ℂ × ℂ | alpha N ≤ p.1.re ∧ p.1.re ≤ beta ∧
      alpha N ≤ p.2.re ∧ p.2.re ≤ beta} ⊆ analyticDomain := by
  intro p hp
  have ha := large_alpha_pos hlarge
  exact ⟨lt_of_lt_of_le ha hp.1, lt_of_le_of_lt hp.2.1 (by norm_num [beta]),
    lt_of_lt_of_le ha hp.2.2.1, lt_of_le_of_lt hp.2.2.2 (by norm_num [beta])⟩

theorem proposition_5_1 (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) :
    HermitianKernel (weightedKernel N) ∧
    HermitianKernel (fun s z => residual N s (conj z)) ∧
    DifferentiableOn ℂ (fun p : ℂ × ℂ => weightedKernel N p.1 (conj p.2)) analyticDomain ∧
    (∃ U : Set (ℂ × ℂ), IsOpen U ∧
      {p | alpha N ≤ p.1.re ∧ p.1.re ≤ beta ∧
        alpha N ≤ p.2.re ∧ p.2.re ≤ beta} ⊆ U ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => residual N p.1 p.2) U ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => weightedKernel N p.1 (conj p.2)) U) ∧
    (∀ s z : ℂ, (s, conj z) ∈ analyticDomain →
      wirtingerBar (fun w => residual N w (conj z)) s = 0 ∧
      wirtinger (fun w => residual N s (conj w)) z = 0) ∧
    1 / 90 < sigmaStar - alpha N ∧ beta - sigmaStar = 1 / 72 := by
  have hpos : 0 < N := by have := (large_parameters hlarge).1; omega
  have hd := weightedKernel_conj_differentiableOn N hpos hGRH
  refine ⟨weightedKernel_hermitian N, residual_hermitian N, hd,
    ⟨analyticDomain, analyticDomain_isOpen, large_closed_strip_subset hlarge,
      residual_differentiableOn N hpos hGRH, hd⟩,
    residual_wirtinger N hpos hGRH, ?_, by norm_num [beta, sigmaStar]⟩
  have hlog : (10 : ℝ) < Real.log N := by
    simpa using Real.log_lt_log (Real.exp_pos 10) hlarge
  have ha : alpha N < 1/10 := one_div_lt_one_div_of_lt (by norm_num) hlog
  dsimp [sigmaStar]
  linarith

lemma weightedKernel_column_differentiableAt (N : ℕ) [NeZero N] (hN : 0 < N) (hGRH : GRH N)
    (s z : ℂ) (hsz : (s,conj z) ∈ analyticDomain) :
    DifferentiableAt ℂ (fun w => weightedKernel N w z) s := by
  have hj : DifferentiableAt ℂ (fun p : ℂ × ℂ => weightedKernel N p.1 (conj p.2)) (s,conj z) :=
    (weightedKernel_conj_differentiableOn N hN hGRH).differentiableAt
      (analyticDomain_isOpen.mem_nhds hsz)
  simpa only [Function.comp_def, Complex.conj_conj] using
    (DifferentiableAt.comp (g := fun p : ℂ × ℂ => weightedKernel N p.1 (conj p.2))
      (f := fun w : ℂ => (w,conj z)) s hj (by fun_prop))

lemma weightedKernel_closed_column_regular (N : ℕ) [NeZero N]
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (z : ℂ)
    (hz : alpha N ≤ z.re ∧ z.re ≤ beta) :
    DifferentiableOn ℂ (fun s => weightedKernel N s z) (strip (alpha N) beta) ∧
    ContinuousOn (fun s => weightedKernel N s z) {s | alpha N ≤ s.re ∧ s.re ≤ beta} := by
  have hpos : 0 < N := by have := (large_parameters hlarge).1; omega
  have hd (s : ℂ) (hs : alpha N ≤ s.re ∧ s.re ≤ beta) :
      DifferentiableAt ℂ (fun w => weightedKernel N w z) s :=
    weightedKernel_column_differentiableAt N hpos hGRH s z
      (large_closed_strip_subset hlarge ⟨hs.1, hs.2, hz.1, hz.2⟩)
  refine ⟨fun s hs => (hd s ⟨hs.1.le, hs.2.le⟩).differentiableWithinAt,
    fun s hs => (hd s hs).continuousAt.continuousWithinAt⟩

theorem proposition_5_1_fueter_equation (N : ℕ) [NeZero N] (hN : Even N)
    (hlarge : Real.exp 10 < (N : ℝ)) (hGRH : GRH N) (s z : ℂ)
    (hsz : (s, conj z) ∈ analyticDomain) :
    fueterOperator (fun u v => residual N u (conj v)) s z = 0 := by
  have hpos : 0 < N := by have := (large_parameters hlarge).1; omega
  have h := residual_wirtinger N hpos hGRH s z hsz
  simp [fueterOperator, h.1, h.2, complexQuaternion]
  rfl

end ConditionalGoldbach
