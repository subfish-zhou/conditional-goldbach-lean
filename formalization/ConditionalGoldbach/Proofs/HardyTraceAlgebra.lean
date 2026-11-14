module

public import ConditionalGoldbach.Definitions.HardyTraces
public import ConditionalGoldbach.Definitions.Hilbert

/-! Linear boundary representation and its exact norm normalization. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

lemma fourierLaplace_integrable {a b : ℝ} (ψ : HardySpace a b) {s : ℂ}
    (hs : s ∈ strip a b) : Integrable (fun τ : ℝ => ψ τ * Complex.exp (s * τ)) := by
  have hm : AEStronglyMeasurable (fun τ : ℝ => ψ τ * Complex.exp (s * τ)) volume :=
    (hardySpace_aestronglyMeasurable ψ).mul (by fun_prop :
      Continuous (fun τ : ℝ => Complex.exp (s * τ))).aestronglyMeasurable
  apply (hardy_weighted_line_integrable hs ψ).norm.mono' hm
  filter_upwards [] with τ
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact le_of_eq (mul_comm _ _)

lemma fourierLaplace_add {a b : ℝ} (ψ χ : HardySpace a b) {s : ℂ}
    (hs : s ∈ strip a b) :
    fourierLaplace (ψ + χ) s = fourierLaplace ψ s + fourierLaplace χ s := by
  unfold fourierLaplace
  rw [← mul_add, ← integral_add (fourierLaplace_integrable ψ hs) (fourierLaplace_integrable χ hs)]
  congr 1
  apply integral_congr_ae
  filter_upwards [(volume_absolutelyContinuous_hardyMeasure a b).ae_eq (Lp.coeFn_add ψ χ)] with τ ht
  simp only [ht, Pi.add_apply, add_mul]

lemma fourierLaplace_smul {a b : ℝ} (c : ℂ) (ψ : HardySpace a b) {s : ℂ}
    (_hs : s ∈ strip a b) : fourierLaplace (c • ψ) s = c * fourierLaplace ψ s := by
  unfold fourierLaplace
  calc
    _ = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * ∫ τ : ℝ, c * (ψ τ * Complex.exp (s * τ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [(volume_absolutelyContinuous_hardyMeasure a b).ae_eq (Lp.coeFn_smul c ψ)] with τ ht
      simp only [ht, Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = _ := by rw [integral_const_mul]; ring

lemma boundaryTraces_spec {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    IsBoundaryTrace hab ψ (boundaryTraces hab ψ).1 (boundaryTraces hab ψ).2 :=
  Classical.choose_spec (boundaryTraces_exist hab ψ)

lemma boundaryTraces_norm_sq {a b : ℝ} (hab : a < b) (ψ : HardySpace a b) :
    ‖ψ‖ ^ 2 = ‖(boundaryTraces hab ψ).1‖ ^ 2 + ‖(boundaryTraces hab ψ).2‖ ^ 2 := by
  have h := boundaryTraces_spec hab ψ
  exact hardy_boundary_norm_of_traces hab ψ _ _ h.1 h.2

lemma interiorLine_add {a b : ℝ} (hab : a < b) (ψ χ : HardySpace a b)
    (x : ℝ) (hx : x ∈ Ioo a b) :
    interiorLine hab (ψ + χ) x hx = interiorLine hab ψ x hx + interiorLine hab χ x hx := by
  apply Lp.ext
  filter_upwards [(interiorLine_memLp hab hx (ψ + χ)).coeFn_toLp,
    (interiorLine_memLp hab hx ψ).coeFn_toLp, (interiorLine_memLp hab hx χ).coeFn_toLp,
    Lp.coeFn_add (interiorLine hab ψ x hx) (interiorLine hab χ x hx)] with t ht htψ htχ htadd
  change ((interiorLine_memLp hab hx (ψ + χ)).toLp _) t = _
  rw [ht, htadd]
  change fourierLaplace (ψ + χ) (line x t) =
    ((interiorLine_memLp hab hx ψ).toLp _) t + ((interiorLine_memLp hab hx χ).toLp _) t
  rw [htψ, htχ]
  exact fourierLaplace_add ψ χ (by simpa only [strip, Set.mem_ofPred_eq, Set.mem_Ioo, line, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    add_zero] using hx)

lemma interiorLine_smul {a b : ℝ} (hab : a < b) (c : ℂ) (ψ : HardySpace a b)
    (x : ℝ) (hx : x ∈ Ioo a b) :
    interiorLine hab (c • ψ) x hx = c • interiorLine hab ψ x hx := by
  apply Lp.ext
  filter_upwards [(interiorLine_memLp hab hx (c • ψ)).coeFn_toLp,
    (interiorLine_memLp hab hx ψ).coeFn_toLp, Lp.coeFn_smul c (interiorLine hab ψ x hx)] with t ht htψ htadd
  change ((interiorLine_memLp hab hx (c • ψ)).toLp _) t = _
  rw [ht, htadd]
  change fourierLaplace (c • ψ) (line x t) = c * ((interiorLine_memLp hab hx ψ).toLp _) t
  rw [htψ]
  exact fourierLaplace_smul c ψ (by simpa only [strip, Set.mem_ofPred_eq, Set.mem_Ioo, line, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    add_zero] using hx)

lemma boundaryTraces_unique {a b : ℝ} (hab : a < b) (ψ : HardySpace a b)
    (p q : Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ))
    (hp : IsBoundaryTrace hab ψ p.1 p.2) (hq : IsBoundaryTrace hab ψ q.1 q.2) : p = q := by
  have : NeBot (comap (Subtype.val : Ioo a b → ℝ) (nhdsWithin a (Ioo a b))) :=
    (left_nhdsWithin_Ioo_neBot hab).comap_of_range_mem
      (by simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : Ioo a b ∈ nhdsWithin a (Ioo a b)))
  have : NeBot (comap (Subtype.val : Ioo a b → ℝ) (nhdsWithin b (Ioo a b))) :=
    (right_nhdsWithin_Ioo_neBot hab).comap_of_range_mem
      (by simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : Ioo a b ∈ nhdsWithin b (Ioo a b)))
  exact Prod.ext (tendsto_nhds_unique hp.1 hq.1) (tendsto_nhds_unique hp.2 hq.2)

lemma boundaryTraces_add {a b : ℝ} (hab : a < b) (ψ χ : HardySpace a b) :
    boundaryTraces hab (ψ + χ) = boundaryTraces hab ψ + boundaryTraces hab χ := by
  apply boundaryTraces_unique hab (ψ + χ) _ _ (boundaryTraces_spec hab (ψ + χ))
  constructor
  · simpa only [← interiorLine_add, Prod.fst_add] using
      (boundaryTraces_spec hab ψ).1.add (boundaryTraces_spec hab χ).1
  · simpa only [← interiorLine_add, Prod.snd_add] using
      (boundaryTraces_spec hab ψ).2.add (boundaryTraces_spec hab χ).2

lemma boundaryTraces_smul {a b : ℝ} (hab : a < b) (c : ℂ) (ψ : HardySpace a b) :
    boundaryTraces hab (c • ψ) = c • boundaryTraces hab ψ := by
  apply boundaryTraces_unique hab (c • ψ) _ _ (boundaryTraces_spec hab (c • ψ))
  constructor
  · simpa only [← interiorLine_smul, Prod.smul_fst] using
      (boundaryTraces_spec hab ψ).1.const_smul c
  · simpa only [← interiorLine_smul, Prod.smul_snd] using
      (boundaryTraces_spec hab ψ).2.const_smul c

lemma boundaryTraces_sub {a b : ℝ} (hab : a < b) (ψ χ : HardySpace a b) :
    boundaryTraces hab (ψ - χ) = boundaryTraces hab ψ - boundaryTraces hab χ := by
  rw [sub_eq_add_neg, boundaryTraces_add, ← neg_one_smul ℂ χ, boundaryTraces_smul, neg_one_smul,
    ← sub_eq_add_neg]

lemma boundaryTraces_norm_sq_sub {a b : ℝ} (hab : a < b) (ψ χ : HardySpace a b) :
    ‖ψ - χ‖ ^ 2 = ‖(boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1‖ ^ 2 +
      ‖(boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2‖ ^ 2 := by
  simpa only [boundaryTraces_sub, Prod.fst_sub, Prod.snd_sub] using boundaryTraces_norm_sq hab (ψ - χ)

theorem lemma_5_2_representation_spec (a b : ℝ) (hab : a < b) :
    (∀ ψ : HardySpace a b,
      (∀ s ∈ strip a b, Integrable (fun τ : ℝ => ψ τ * Complex.exp (s * τ))) ∧
      IsBoundaryTrace hab ψ (boundaryTraces hab ψ).1 (boundaryTraces hab ψ).2 ∧
      Integrable (fun τ : ℝ => ‖ψ τ‖ ^ 2 * hardyWeight a b τ) ∧
      ‖ψ‖ ^ 2 = ∫ τ : ℝ, ‖ψ τ‖ ^ 2 * hardyWeight a b τ) ∧
    (∀ ψ χ : HardySpace a b, ∀ s ∈ strip a b,
      fourierLaplace (ψ + χ) s = fourierLaplace ψ s + fourierLaplace χ s) ∧
    (∀ c : ℂ, ∀ ψ : HardySpace a b, ∀ s ∈ strip a b,
      fourierLaplace (c • ψ) s = c * fourierLaplace ψ s) ∧
    (∀ ψ χ : HardySpace a b,
      boundaryTraces hab (ψ + χ) = boundaryTraces hab ψ + boundaryTraces hab χ) ∧
    (∀ c : ℂ, ∀ ψ : HardySpace a b,
      boundaryTraces hab (c • ψ) = c • boundaryTraces hab ψ) ∧
    (∀ ψ χ : HardySpace a b, ‖ψ - χ‖ ^ 2 =
      ‖(boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1‖ ^ 2 +
      ‖(boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2‖ ^ 2) := by
  exact ⟨fun ψ => ⟨fun _ hs => fourierLaplace_integrable ψ hs, boundaryTraces_spec hab ψ,
    hardySpace_integrable_weighted_sq ψ, hardySpace_norm_sq_integral ψ⟩,
    fun ψ χ _ hs => fourierLaplace_add ψ χ hs,
    fun c ψ _ hs => fourierLaplace_smul c ψ hs,
    boundaryTraces_add hab, boundaryTraces_smul hab, boundaryTraces_norm_sq_sub hab⟩

lemma boundaryTraces_lipschitz {a b : ℝ} (hab : a < b) :
    LipschitzWith 1 (boundaryTraces hab) := by
  apply LipschitzWith.of_dist_le_mul
  intro ψ χ
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Prod.norm_def]
  have h := boundaryTraces_norm_sq_sub hab ψ χ
  apply max_le
  · have h0 := norm_nonneg (ψ - χ)
    have h1 := norm_nonneg ((boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1)
    simpa only [Prod.fst_sub] using (show ‖(boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1‖ ≤ ‖ψ - χ‖ by
      nlinarith [sq_nonneg (‖(boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2‖)])
  · have h0 := norm_nonneg (ψ - χ)
    have h1 := norm_nonneg ((boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2)
    simpa only [Prod.snd_sub] using (show ‖(boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2‖ ≤ ‖ψ - χ‖ by
      nlinarith [sq_nonneg (‖(boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1‖)])

lemma boundaryTraces_antilipschitz {a b : ℝ} (hab : a < b) :
    AntilipschitzWith 2 (boundaryTraces hab) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro ψ χ
  simp only [NNReal.coe_ofNat, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  have h := boundaryTraces_norm_sq_sub hab ψ χ
  have h0 := norm_nonneg (ψ - χ)
  have h1 := norm_nonneg ((boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1)
  have h2 := norm_nonneg ((boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2)
  have hle1 := le_max_left ‖(boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1‖
    ‖(boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2‖
  have hle2 := le_max_right ‖(boundaryTraces hab ψ).1 - (boundaryTraces hab χ).1‖
    ‖(boundaryTraces hab ψ).2 - (boundaryTraces hab χ).2‖
  have hm0 := le_trans h1 hle1
  have hs1 := (sq_le_sq₀ h1 hm0).mpr hle1
  have hs2 := (sq_le_sq₀ h2 hm0).mpr hle2
  nlinarith

theorem lemma_5_2_closed_trace_space (a b : ℝ) (hab : a < b) :
    IsClosed (Set.range (fun ψ : HardySpace a b => boundaryTraces hab ψ)) :=
  (boundaryTraces_antilipschitz hab).isClosed_range (boundaryTraces_lipschitz hab).uniformContinuous

/-- The original trace pair, now viewed with its Hilbert direct-sum norm. -/
def hardyTraceIsometry {a b : ℝ} (hab : a < b) :
    HardySpace a b →ₗᵢ[ℂ] WithLp 2
      (Lp ℂ 2 (volume : Measure ℝ) × Lp ℂ 2 (volume : Measure ℝ)) where
  toFun ψ := WithLp.toLp 2 (boundaryTraces hab ψ)
  map_add' ψ χ := by simp only [boundaryTraces_add, WithLp.toLp_add]
  map_smul' c ψ := by simp only [boundaryTraces_smul, WithLp.toLp_smul, RingHom.id_apply]
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact (boundaryTraces_norm_sq hab ψ).symm

theorem lemma_5_2_boundary_inner (a b : ℝ) (hab : a < b) (h g : HardySpace a b) :
    paperInner h g =
      (∫ t : ℝ, (boundaryTraces hab h).1 t * conj ((boundaryTraces hab g).1 t)) +
      ∫ t : ℝ, (boundaryTraces hab h).2 t * conj ((boundaryTraces hab g).2 t) := by
  have hi := (hardyTraceIsometry hab).inner_map_map g h
  change inner ℂ (WithLp.toLp 2 (boundaryTraces hab g))
    (WithLp.toLp 2 (boundaryTraces hab h)) = inner ℂ g h at hi
  simp only [WithLp.prod_inner_apply] at hi
  rw [paperInner, ← hi, L2.inner_def, L2.inner_def]
  congr 1

lemma fourierLaplace_injective_strip {a b : ℝ} (hab : a < b) (ψ χ : HardySpace a b)
    (h : ∀ s ∈ strip a b, fourierLaplace ψ s = fourierLaplace χ s) : ψ = χ := by
  have hi : (fun x : Ioo a b => interiorLine hab ψ x x.property) =
      (fun x : Ioo a b => interiorLine hab χ x x.property) := by
    funext x
    apply Lp.ext
    filter_upwards [(interiorLine_memLp hab x.property ψ).coeFn_toLp,
      (interiorLine_memLp hab x.property χ).coeFn_toLp] with t ht ht'
    change ((interiorLine_memLp hab x.property ψ).toLp _) t =
      ((interiorLine_memLp hab x.property χ).toLp _) t
    rw [ht, ht']
    apply h
    simpa only [strip, Set.mem_ofPred_eq, Set.mem_Ioo, line, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] using x.property
  have hc := boundaryTraces_spec hab χ
  change Tendsto _ _ _ ∧ Tendsto _ _ _ at hc
  rw [← hi] at hc
  have hb := boundaryTraces_unique hab ψ _ _ (boundaryTraces_spec hab ψ) hc
  apply (hardyTraceIsometry hab).injective
  change WithLp.toLp 2 (boundaryTraces hab ψ) = WithLp.toLp 2 (boundaryTraces hab χ)
  rw [hb]

end ConditionalGoldbach
